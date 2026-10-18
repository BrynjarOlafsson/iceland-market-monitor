#!/usr/bin/env python3
"""Discover verified articles and CAPE coverage for Iceland Market Monitor.

Designed to run from the existing GitHub Actions workflow. Discovery is
best-effort: sources may block automated traffic or omit recently published
articles. Only verified publisher pages are ever added to articles.json.

Keep the hand-curated archive intact. No commercial search API key required.
"""
from __future__ import annotations

import argparse
import os
from datetime import datetime, timezone
from email.utils import parsedate_to_datetime
from html import unescape
import json
from pathlib import Path
import re
import sys
import tempfile
import time
from unittest.mock import patch
from urllib.error import HTTPError
from urllib.parse import parse_qs, urlencode, urljoin, urlsplit, urlunsplit
from urllib.request import Request, urlopen
import xml.etree.ElementTree as ET
import unicodedata

from bs4 import BeautifulSoup

ARCHIVE_PATH = Path(__file__).with_name('articles.json')
AUTHOR = 'brynjar orn olafsson'
VISIR_LISTINGS = (
    'https://www.visir.is/f/umraedan',
    'https://www.visir.is/f/umraedan/1',
    'https://www.visir.is/f/innherji',
)
# Optional HTML fallbacks for the RSS feed (some environments block these too).
VB_LISTINGS = (
    'https://vb.is/frettir/',
    'https://vb.is/skodun/',
)
# This URL is a diagnostic probe only; it is NEVER added as a discovery lead.
KNOWN_ARTICLE_URL = (
    'https://www.visir.is/g/20262942290d/'
    'verdlagning-hlutabrefa-enn-hofleg-i-sogulegu-samhengi'
)
VB_RSS = 'https://www.vb.is/rss/'
MONTHS = {
    'janúar': 1, 'febrúar': 2, 'mars': 3, 'apríl': 4, 'maí': 5, 'júní': 6,
    'júlí': 7, 'ágúst': 8, 'september': 9, 'október': 10, 'nóvember': 11,
    'desember': 12,
}
# Search-query results are only leads, never proof of author or attribution.
SEARCH_QUERIES = (
    '"Brynjar Örn Ólafsson" site:visir.is/g/',
    '"Brynjar Örn Ólafsson" site:vb.is',
    '"Brynjar" "CAPE" site:visir.is/g/',
    '"Brynjar" "CAPE" site:vb.is/frettir/',
    '"OMXI15" "CAPE" site:vb.is',
)
SEARCH_HEADLINE_TERMS = (
    'cape', 'omxi', 'urvalsvisit', 'hlutabref', 'verdlagning', 'eignaverd', 'brynjar',
)
MAX_PAGE_BYTES = 3_000_000
MAX_CANDIDATES = 90
MAX_REVIEW = 15

# Optional public news-index discovery. GDELT supplies *links*, not verified
# publication text or authorship; only publisher pages can establish those.
GDELT_QUERY = 'domainis:vb.is (CAPE OR OMXI15 OR Brynjar)'
# Respect rate limits. Only retry once if the server specifically requests a
# short wait. Long or unspecified waits are left to the next daily run.
GDELT_RETRY_MAX_SECONDS = 8


def normalized(text: str) -> str:
    value = unicodedata.normalize('NFD', (text or '').replace('\u00ad', '').replace('\u200b', ''))
    return ''.join(ch for ch in value if not unicodedata.combining(ch)).casefold()


def allowed_publisher(url: str) -> str | None:
    parts = urlsplit(url)
    if parts.scheme != 'https' or parts.username or parts.password or parts.port:
        return None
    host = (parts.hostname or '').lower()
    if host in ('www.visir.is', 'visir.is') and re.match(r'^/g/[^/]+', parts.path):
        return 'Innherji'
    if host in ('www.vb.is', 'vb.is') and parts.path.startswith(('/frettir/', '/skodun/')):
        return 'Viðskiptablaðið'
    return None


def canonical(url: str) -> str:
    parts = urlsplit(url)
    host = (parts.hostname or '').lower().removeprefix('www.')
    path = parts.path.rstrip('/')
    # Vísir pages often have /g/{id}/f/skodanir; these are the same article.
    if host == 'visir.is' and re.match(r'^/g/[^/]+/', path):
        path = '/'.join(path.split('/')[:4])
    return urlunsplit((parts.scheme.lower(), host, path, '', ''))


def retry_after_seconds(value: str | None) -> float | None:
    """Parse Retry-After as seconds or HTTP date; None means do not retry."""
    if not value:
        return None
    try:
        return max(0.0, float(value.strip()))
    except ValueError:
        try:
            date = parsedate_to_datetime(value)
            if date.tzinfo is None:
                date = date.replace(tzinfo=timezone.utc)
            return max(0.0, (date - datetime.now(timezone.utc)).total_seconds())
        except (ValueError, TypeError, IndexError):
            return None


def get_bytes(url: str) -> bytes:
    request = Request(url, headers={
        'User-Agent': 'Mozilla/5.0 (compatible; IcelandMarketMonitor/0.7; public-article-monitor)',
        'Accept': 'application/rss+xml, application/atom+xml, application/xml, text/html;q=0.9, */*;q=0.5',
        'Accept-Language': 'is,en;q=0.7',
    })
    gdelt = urlsplit(url).hostname == 'api.gdeltproject.org'
    try:
        with urlopen(request, timeout=20) as response:
            return response.read(MAX_PAGE_BYTES + 1)[:MAX_PAGE_BYTES]
    except HTTPError as exc:
        if not (gdelt and exc.code == 429):
            raise
        wait = retry_after_seconds(exc.headers.get('Retry-After'))
        if wait is None or wait > GDELT_RETRY_MAX_SECONDS:
            print('GDELT RATE LIMITED: HTTP 429; no short Retry-After provided. '
                  'Skipping until next scheduled check.', file=sys.stderr)
            raise
        print(f'GDELT RATE LIMITED: waiting {wait:.1f}s before one retry.', file=sys.stderr)
        time.sleep(wait)
        # Exactly one retry; any repeated 429 propagates to safe_fetch.
        with urlopen(request, timeout=20) as response:
            return response.read(MAX_PAGE_BYTES + 1)[:MAX_PAGE_BYTES]


def safe_fetch(url: str) -> bytes | None:
    try:
        return get_bytes(url)
    except Exception as exc:
        print(f'  WARNING {url}: {exc}', file=sys.stderr)
        return None


def search_feed_urls() -> list[tuple[str, str]]:
    """Independent search feeds; a 403/429 is reported and other feeds continue."""
    feeds = []
    for query in SEARCH_QUERIES:
        bing = 'https://www.bing.com/search?' + urlencode({'q': query, 'format': 'rss', 'setlang': 'is'})
        feeds.append(('Bing RSS: ' + query, bing))
    # Google News is an *additional* discovery signal. Its item URLs sometimes
    # point to news.google.com rather than the publisher and may be unusable.
    google = 'https://news.google.com/rss/search?' + urlencode({
        'q': '"Brynjar Örn Ólafsson"', 'hl': 'is', 'gl': 'IS', 'ceid': 'IS:is'})
    feeds.append(('Google News RSS: author', google))
    cape_news = 'https://news.google.com/rss/search?' + urlencode({
        'q': '"OMXI15" "CAPE"', 'hl': 'is', 'gl': 'IS', 'ceid': 'IS:is'})
    feeds.append(('Google News RSS: OMXI15 CAPE', cape_news))
    return feeds


def gdelt_feed_urls() -> list[tuple[str, str]]:
    """ONE narrow vb.is news-index request per run (reduce 429 pressure).

    GDELT is a discovery aid only. An empty/rate-limited response is never
    evidence that there were no new relevant articles.
    """
    url = 'https://api.gdeltproject.org/api/v2/doc/doc?' + urlencode({
        'query': GDELT_QUERY, 'mode': 'artlist', 'format': 'json',
        'timespan': '3months', 'maxrecords': 50, 'sort': 'datedesc',
    })
    return [('GDELT: combined vb.is CAPE/OMXI15/Brynjar', url)]


def discover_gdelt_links(raw: bytes) -> list[tuple[str, None]]:
    """Extract original publisher URLs from the news index.

    GDELT `seendate` is not the publication date, so no date hint is used.
    """
    payload = json.loads(raw.decode('utf-8-sig'))
    if not isinstance(payload, dict):
        raise ValueError('GDELT result is not an object')
    articles = payload.get('articles', [])
    if not isinstance(articles, list):
        raise ValueError('GDELT articles is not an array')
    result = []
    for row in articles[:250]:
        if not isinstance(row, dict):
            continue
        link = row.get('url') or row.get('url_mobile') or ''
        link = publisher_link(str(link))
        if link and allowed_publisher(link) == 'Viðskiptablaðið':
            result.append((link, None))
    return list(dict.fromkeys(result))


def publisher_link(url: str) -> str | None:
    """Keep direct publisher URLs, or unwrap a publisher link from a redirect URL."""
    if allowed_publisher(url):
        return url
    parts = urlsplit(url)
    for param in ('url', 'u', 'q', 'target'):
        for target in parse_qs(parts.query).get(param, []):
            if allowed_publisher(target):
                return target
    return None


def rss_items(xml: bytes) -> list[tuple[str, str, str | None]]:
    """Return (url, title+description, date); supports RSS and Atom."""
    root = ET.fromstring(xml)
    records = []
    if root.tag.endswith('rss') or root.find('channel') is not None:
        for item in root.findall('.//item')[:120]:
            link = (item.findtext('link') or '').strip()
            desc = BeautifulSoup(item.findtext('description') or '', 'html.parser').get_text(' ', strip=True)
            title = (item.findtext('title') or '') + ' ' + desc
            records.append((link, unescape(title), item.findtext('pubDate')))
    else:
        ns = '{http://www.w3.org/2005/Atom}'
        for item in root.findall(f'.//{ns}entry')[:120]:
            links = item.findall(f'{ns}link')
            link = next((a.get('href', '') for a in links if a.get('rel', 'alternate') == 'alternate'), '')
            title = item.findtext(f'{ns}title') or ''
            summary = item.findtext(f'{ns}summary') or ''
            date = item.findtext(f'{ns}published') or item.findtext(f'{ns}updated')
            records.append((link, unescape(title + ' ' + summary), date))
    return records


def discover_search_feed(xml: bytes) -> list[tuple[str, str | None]]:
    """Search-feed links are candidates, not verified claims."""
    links = []
    for link, snippet, date in rss_items(xml):
        target = publisher_link(link)
        if not target:
            # Google News snippets sometimes contain the original article link.
            for found in re.findall(r'https?://[^\s"<>]+', snippet):
                target = publisher_link(unescape(found.rstrip(').,;')))
                if target:
                    break
        if target:
            links.append((target, date))
    return list(dict.fromkeys(links))


def discover_visir_links(html: bytes, base_url: str) -> list[str]:
    """Only author-matched cards; do not accidentally match adjacent cards."""
    soup = BeautifulSoup(html, 'html.parser')
    links = []
    for a in soup.select('a[href*="/g/"]'):
        url = urljoin(base_url, a.get('href', ''))
        if allowed_publisher(url) != 'Innherji':
            continue
        current = a
        for _ in range(6):
            current = current.parent
            if current is None:
                break
            neighbours = {canonical(urljoin(base_url, x.get('href', '')))
                          for x in current.select('a[href*="/g/"]')}
            if len(neighbours) > 1:
                break
            text = normalized(current.get_text(' ', strip=True))
            if len(text) > 1400:
                break
            if AUTHOR in text:
                links.append(url)
                break
    return list(dict.fromkeys(links))


def discover_vb_links(xml: bytes) -> list[tuple[str, str | None]]:
    links = []
    for link, text, date in rss_items(xml):
        if allowed_publisher(link) != 'Viðskiptablaðið':
            continue
        if any(word in normalized(text) for word in SEARCH_HEADLINE_TERMS):
            links.append((link, date))
    return list(dict.fromkeys(links))


def discover_vb_listing_links(html: bytes, base_url: str) -> list[tuple[str, str | None]]:
    """Use category pages as backup leads; final publication requires page verification.

    Do not infer authorship from the listing, and do not accept unrelated news.
    """
    soup = BeautifulSoup(html, 'html.parser')
    links = []
    for a in soup.select('a[href]'):
        url = urljoin(base_url, a.get('href', ''))
        if allowed_publisher(url) != 'Viðskiptablaðið':
            continue
        label = normalized(a.get_text(' ', strip=True))
        if any(term in label for term in SEARCH_HEADLINE_TERMS):
            links.append((url, None))
    return list(dict.fromkeys(links))[:150]


def first_meta(soup: BeautifulSoup, keys: tuple[str, ...]) -> str:
    for key in keys:
        tag = soup.find('meta', attrs={'property': key}) or soup.find('meta', attrs={'name': key})
        if tag and tag.get('content'):
            return tag['content'].strip()
    return ''


def json_ld_objects(soup: BeautifulSoup) -> list[dict]:
    results = []
    for tag in soup.find_all('script', attrs={'type': 'application/ld+json'}):
        try:
            item = json.loads(tag.string or tag.get_text())
        except (ValueError, TypeError):
            continue
        stack = [item]
        while stack:
            node = stack.pop()
            if isinstance(node, list):
                stack.extend(node)
            elif isinstance(node, dict):
                results.append(node)
                if '@graph' in node:
                    stack.append(node['@graph'])
    return results


def author_of_ld(soup: BeautifulSoup) -> str:
    authors = []
    for obj in json_ld_objects(soup):
        byline = obj.get('author', [])
        for entry in byline if isinstance(byline, list) else [byline]:
            authors.append(entry.get('name', '') if isinstance(entry, dict) else str(entry))
    return ' '.join(authors)


def body_text(soup: BeautifulSoup) -> str:
    doc = (soup.select_one('article') or
           soup.select_one('[itemprop="articleBody"]') or
           soup.select_one('main'))
    if doc is None:
        # No reliable article body: cannot verify third-party attribution.
        return ''
    clone = BeautifulSoup(str(doc), 'html.parser')
    for elem in clone.select('aside, nav, footer, script, style, [class*="related"], [class*="Related"]'):
        elem.decompose()
    return clone.get_text(' ', strip=True)


def parse_date_string(value: str) -> str | None:
    if not value:
        return None
    try:
        return datetime.fromisoformat(value.strip().replace('Z', '+00:00')).date().isoformat()
    except ValueError:
        pass
    try:
        return parsedate_to_datetime(value).date().isoformat()
    except (ValueError, TypeError, IndexError):
        pass
    match = re.search(r'(\d{1,2})\.\s*(' + '|'.join(MONTHS) + r')\s+(20\d{2})', value, re.I)
    if match:
        day, month, year = match.groups()
        try:
            return datetime(int(year), MONTHS[month.lower()], int(day)).date().isoformat()
        except ValueError:
            pass
    return None


def published_date(soup: BeautifulSoup, fallback: str | None) -> str | None:
    values = [first_meta(soup, ('article:published_time', 'datePublished', 'pubdate', 'date'))]
    values.extend(str(obj.get('datePublished', '')) for obj in json_ld_objects(soup))
    when = soup.find('time', attrs={'datetime': True})
    if when:
        values.append(when.get('datetime', ''))
    values.append(soup.get_text(' ', strip=True)[:1300])
    if fallback:
        values.append(fallback)
    for item in values:
        date = parse_date_string(item)
        if date:
            return date
    return None


def topic_of(title: str) -> str:
    text = normalized(title)
    if any(t in text for t in ('innherja', 'mar ', 'eftirlit', 'regluverk', 'tilbodabreyting')):
        return 'Regluverk og markaðir'
    if any(t in text for t in ('cape', 'hlutabref', 'omxi', 'hagnad', 'eignaverd', 'kaupholl', 'urvalsvisit')):
        return 'Hlutabréf og eignaverð'
    if any(t in text for t in ('skuldabref', 'vaxt', 'vext', 'verdtrygg', 'rikisbr')):
        return 'Skuldabréf og vextir'
    return 'Þjóðhagfræði'


def describe_candidate(url: str, html: bytes, source: str, date_hint: str | None = None) -> dict | None:
    """Strict verification: explicit byline OR CAPE + named attribution in article body."""
    if allowed_publisher(url) != source:
        return None
    soup = BeautifulSoup(html, 'html.parser')
    title = first_meta(soup, ('og:title', 'twitter:title'))
    if not title:
        title = soup.h1.get_text(' ', strip=True) if soup.h1 else ''
    title = re.sub(r'\s+[|–-]\s+(Innherji|Vísir|Viðskiptablaðið)\s*$', '', title).strip()
    if not title:
        return None
    date = published_date(soup, date_hint)
    if not date or date > datetime.now(timezone.utc).date().isoformat():
        return None

    # An article can mention Brynjar in a generic footer or CAPE methodology
    # note. Such a reference is NOT evidence that Brynjar authored the article.
    byline = normalized(' '.join((
        first_meta(soup, ('author', 'article:author', 'byl')),
        author_of_ld(soup),
    )))
    # Some Icelandic publishers display the byline beside the headline,
    # without author metadata. Restrict this fallback to the headline region
    # so an author's name in the article's CAPE background note is not
    # mistaken for evidence of authorship.
    h1 = soup.find('h1')
    headline_context = []
    if h1:
        for node in (h1.parent, h1.parent.parent if h1.parent else None):
            if node:
                fragment = node.get_text(' ', strip=True)
                if len(fragment) < 1800:
                    headline_context.append(fragment)
    author_near_title = normalized(' '.join(headline_context))
    authored = (AUTHOR in byline or bool(re.search(
        r'\bbrynjar orn olafsson\s+skrifar\b', author_near_title)))

    if authored:
        kind = 'authored'
    else:
        content = normalized(body_text(soup))
        named = [match.start() for match in re.finditer(re.escape(AUTHOR), content)]
        capes = [match.start() for match in re.finditer(r'\bcape\b', content)]
        # Must explicitly cite the person and CAPE in close proximity within
        # the actual article body, not merely a generic page footer/sidebar.
        if not named or not capes or not any(abs(n-c) <= 450 for n in named for c in capes):
            return None
        kind = 'coverage'

    desc = first_meta(soup, ('og:description', 'description'))
    desc = re.sub(r'\s+', ' ', BeautifulSoup(desc, 'html.parser').get_text(' ', strip=True)).strip()[:250]
    if not desc:
        desc = ('Fjölmiðlaumfjöllun sem vísar í CAPE-gögn.' if kind == 'coverage'
                else 'Grein eftir Brynjar Örn Ólafsson.')
    return {
        'title': unescape(title), 'date': date, 'year': int(date[:4]),
        'source': source, 'kind': kind,
        'topic': 'Hlutabréf og eignaverð' if kind == 'coverage' else topic_of(title),
        'url': url, 'description': desc, 'extra_links': [],
    }


def emit_warning(message: str) -> None:
    """Produce an actionable warning in the GitHub Actions annotations UI."""
    print('WARNING: ' + message)
    if os.environ.get('GITHUB_ACTIONS') == 'true':
        print('::warning title=Article discovery::' + message.replace('\n', ' '))


def save_archive_atomically(archive_path: Path, data: dict) -> None:
    """Write archive only after full validation; never truncate on error."""
    tmp_name = None
    try:
        with tempfile.NamedTemporaryFile('w', encoding='utf-8',
                                         dir=archive_path.parent,
                                         prefix='.articles_', suffix='.json',
                                         delete=False) as handle:
            tmp_name = handle.name
            json.dump(data, handle, ensure_ascii=False, indent=2)
            handle.write('\n')
        os.replace(tmp_name, archive_path)
    finally:
        if tmp_name and os.path.exists(tmp_name):
            os.unlink(tmp_name)


def add_manually_reviewed_article(archive_path: Path, url: str, title: str,
                                  date: str, kind: str, description: str) -> bool:
    """Explicit curator-controlled fallback for publishers that block robots.

    This mode NEVER guesses authorship or publication date. The person invoking
    it must check these details against the publisher before confirming.
    """
    source = allowed_publisher(url)
    if source is None:
        raise ValueError('Manual entry requires a supported direct HTTPS publisher URL')
    if kind not in ('authored', 'coverage'):
        raise ValueError('Manual kind must be authored or coverage')
    try:
        parsed_date = datetime.strptime(date, '%Y-%m-%d').date()
    except ValueError as exc:
        raise ValueError('Manual date must be a real YYYY-MM-DD date') from exc
    if parsed_date > datetime.now(timezone.utc).date():
        raise ValueError('Manual publication date cannot be in the future')
    if not title.strip() or len(title) > 300 or len(description) > 800:
        raise ValueError('Manual title must be 1–300 chars; description at most 800')
    data = json.loads(archive_path.read_text(encoding='utf-8'))
    if not isinstance(data, dict) or not isinstance(data.get('articles'), list):
        raise ValueError('Invalid articles.json structure')
    if any(canonical(record.get('url') or '') == canonical(url)
           for record in data['articles']):
        print(f'MANUAL NO CHANGE: already archived: {url}')
        return False
    data['articles'].append({
        'title': title.strip(), 'date': date, 'year': parsed_date.year,
        'source': source, 'kind': kind,
        'topic': 'Hlutabréf og eignaverð' if kind == 'coverage' else topic_of(title),
        'url': url, 'description': description.strip() or (
            'Fjölmiðlaumfjöllun sem vísar í CAPE-gögn.' if kind == 'coverage'
            else 'Grein eftir Brynjar Örn Ólafsson.'),
        'extra_links': [],
    })
    data['articles'].sort(key=lambda row: (
        row.get('date') or f"{row.get('year', 0)}-01-01", row.get('title', '')),
        reverse=True)
    save_archive_atomically(archive_path, data)
    print(f'MANUAL ADDED: {date} | {kind} | {source} | {title.strip()}')
    return True


def probe_known_article() -> bool:
    """Diagnostic only: prove a known publisher page remains parsable.

    Deliberately never contributes a discovery lead or modifies the archive.
    """
    raw = safe_fetch(KNOWN_ARTICLE_URL)
    if raw is None:
        print('PROBE UNAVAILABLE: known October Innherji article could not be fetched')
        return False
    result = describe_candidate(KNOWN_ARTICLE_URL, raw, 'Innherji')
    passed = bool(result and result['kind'] == 'authored' and result['date'] == '2026-10-01')
    print(('PROBE PASS' if passed else 'PROBE FAIL') +
          ': known October 2026 article page, authorship and date verification')
    return passed


def update(archive_path: Path = ARCHIVE_PATH, dry_run: bool = False,
           run_probe: bool = True) -> tuple[int, int]:
    data = json.loads(archive_path.read_text(encoding='utf8'))
    if not isinstance(data, dict) or not isinstance(data.get('articles'), list):
        raise ValueError('Expected articles.json to contain an articles array')
    archive = data['articles']
    known = {canonical(rec['url']) for rec in archive if rec.get('url')}
    candidates: dict[str, tuple[str, str, str | None]] = {}
    retrieved = 0
    positive = 0
    empty = 0
    unavailable = 0

    probe_ok = probe_known_article() if run_probe else None

    def record(url: str, date_hint: str | None = None) -> None:
        publisher = allowed_publisher(url)
        if publisher:
            key = canonical(url)
            if key not in candidates:
                candidates[key] = (url, publisher, date_hint)

    def collect(name: str, url: str, parser) -> None:
        nonlocal retrieved, positive, empty, unavailable
        raw = safe_fetch(url)
        if raw is None:
            unavailable += 1
            print(f'SOURCE UNAVAILABLE: {name}')
            return
        try:
            matches = parser(raw)
        except (ET.ParseError, ValueError) as exc:
            unavailable += 1
            print(f'SOURCE INVALID: {name}: {exc}')
            return
        retrieved += 1
        if matches:
            positive += 1
        else:
            empty += 1
        before = len(candidates)
        for link, date in matches:
            record(link, date)
        print(f'SOURCE OK: {name}: {len(matches)} leads; '
              f'{len(candidates)-before} distinct candidates')

    for page in VISIR_LISTINGS:
        collect('Innherji listing (' + page.rsplit('/', 1)[-1] + ')', page,
                lambda raw, page=page: [(url, None) for url in discover_visir_links(raw, page)])
    collect('Viðskiptablaðið RSS', VB_RSS, discover_vb_links)
    for page in VB_LISTINGS:
        collect('Viðskiptablaðið HTML listing (' + page.rsplit('/', 2)[-2] + ')', page,
                lambda raw, page=page: discover_vb_listing_links(raw, page))
    for name, feed_url in search_feed_urls():
        collect(name, feed_url, discover_search_feed)
    for name, feed_url in gdelt_feed_urls():
        collect(name, feed_url, discover_gdelt_links)

    if not retrieved:
        raise RuntimeError('No article-discovery sources were accessible; archive unchanged')

    rejected = 0
    article_failures = 0
    added = []
    manual_review = []
    unarchived_total = sum(1 for key in candidates if key not in known)
    to_check = [item for key, item in candidates.items() if key not in known][:MAX_CANDIDATES]
    for url, publisher, date_hint in to_check:
        raw = safe_fetch(url)
        if raw is None:
            article_failures += 1
            manual_review.append((url, 'publisher page inaccessible'))
            continue
        result = describe_candidate(url, raw, publisher, date_hint)
        if result is None:
            rejected += 1
            # A search-index snippet is not evidence of authorship or CAPE
            # attribution; report for manual review rather than auto-publish.
            if publisher == 'Viðskiptablaðið':
                manual_review.append((url, 'authorship/CAPE attribution not verified'))
            continue
        key = canonical(result['url'])
        if key not in known:
            known.add(key)
            archive.append(result)
            added.append(result)

    print(f'SUMMARY: sources_ok={retrieved}, sources_with_leads={positive}, '
          f'sources_empty={empty}, sources_unavailable={unavailable}, '
          f'unique_candidates={len(candidates)}, already_archived={len(candidates)-unarchived_total}, '
          f'unarchived_checked={len(to_check)}, page_fetch_failures={article_failures}, '
          f'not_verified={rejected}, review_candidates={len(manual_review)}, new_verified={len(added)}')

    if manual_review:
        print('MANUAL REVIEW: candidates are NOT published until authorship or a '
              'CAPE attribution is verified on the publisher page:')
        for url, reason in manual_review[:MAX_REVIEW]:
            print(f'  REVIEW {reason}: {url}')
        if len(manual_review) > MAX_REVIEW:
            print(f'  REVIEW TRUNCATED: {len(manual_review) - MAX_REVIEW} additional candidates')
        # Present links on the Actions run Summary without changing any site data.
        summary_path = os.environ.get('GITHUB_STEP_SUMMARY')
        if summary_path:
            with open(summary_path, 'a', encoding='utf8') as handle:
                handle.write('\n### Article-discovery manual review\n')
                handle.write('These are leads only, **not verified publications**.\n\n')
                for url, reason in manual_review[:MAX_REVIEW]:
                    # Original publisher URLs were validated by allowed_publisher.
                    handle.write(f'- {reason}: {url}\n')

    if added and not dry_run:
        archive.sort(key=lambda r: (r.get('date') or f"{r.get('year', 0)}-01-01", r.get('title', '')), reverse=True)
        save_archive_atomically(archive_path, data)
        print(f'ARCHIVE SAVED: {archive_path} ({len(archive)} total entries)')
    elif dry_run:
        print('DRY RUN: no file written')
    else:
        print('NO CHANGE: no newly verified publications; existing archive preserved')

    # A success is a best-effort discovery check, never a completeness guarantee.
    # Crucially, a successful direct probe does not establish that discovery works.
    degraded = bool(unavailable or article_failures or manual_review or not positive or probe_ok is False)
    if degraded:
        reasons = []
        if unavailable:
            reasons.append(f'{unavailable} source(s) unavailable')
        if article_failures:
            reasons.append(f'{article_failures} candidate article(s) inaccessible')
        if not positive:
            reasons.append('no discovery source supplied leads')
        if manual_review:
            reasons.append(f'{len(manual_review)} link(s) require manual verification')
        if probe_ok is False:
            reasons.append('known-article verification probe failed')
        emit_warning('PARTIAL DISCOVERY: ' + '; '.join(reasons) +
                     '. A zero-new-article result does not prove completeness.')
    else:
        print('DISCOVERY CHECK: sources returned leads and no fetch errors; '
              'new-publication coverage is still best-effort.')
    if unarchived_total > MAX_CANDIDATES:
        emit_warning(f'Candidate processing capped at {MAX_CANDIDATES}; '
                     'some articles were not reviewed in this run')
    for entry in added:
        print(f"ADDED: {entry['date']} | {entry['kind']} | {entry['source']} | {entry['title']}")
    return len(candidates), len(added)


def self_test() -> None:
    """Exercise discovery -> verification -> archival insert WITHOUT touching production.

    The known October article is removed from a temporary copy. Mock publisher
    responses then test both discovery and categorization deterministically.
    This does not test live search feed reachability or recall.
    """
    from contextlib import redirect_stdout
    import io
    known = canonical(KNOWN_ARTICLE_URL)
    original = json.loads(ARCHIVE_PATH.read_text(encoding='utf8'))
    original['articles'] = [x for x in original['articles']
                            if canonical(x.get('url') or '') != known]
    known_html = f"""<!doctype html><html><head>
      <meta property="og:title" content="Verðlagning hlutabréfa enn hófleg í sögulegu samhengi">
      <meta property="article:published_time" content="2026-10-01T08:19:00Z">
      <meta name="author" content="Brynjar Örn Ólafsson"></head>
      <body><article><h1>Verðlagning hlutabréfa enn hófleg í sögulegu samhengi</h1>
      <p>Verðlagning OMXI15 CAPE.</p></article></body></html>""".encode()
    listing_html = f"""<html><body><article>
       <a href="{KNOWN_ARTICLE_URL}">Verðlagning hlutabréfa enn hófleg í sögulegu samhengi</a>
       <div>Brynjar Örn Ólafsson skrifar</div></article>
       <article><a href="/g/20260000000d/unrelated">Önnur frétt</a>
       <div>Annar höfundur skrifar</div></article></body></html>""".encode()
    unrelated_html = """<html><head><meta property="og:title" content="Óskyld frétt"/>
       <meta property="article:published_time" content="2026-09-01"/>
       <meta name="author" content="Annar höfundur"/></head>
       <body><article><p>Engin umfjöllun um CAPE.</p></article></body></html>""".encode()
    def mock_fetch(url):
        if canonical(url) == known:
            return known_html
        if url == VISIR_LISTINGS[0]:
            return listing_html
        if url.endswith('/g/20260000000d/unrelated'):
            return unrelated_html
        # Return parseable empty feeds for the other discovery sources.
        if 'api.gdeltproject.org' in url:
            return b'{"articles": []}'
        if ('rss' in url or 'search?' in url):
            return b'<rss><channel></channel></rss>'
        return b'<html><body></body></html>'

    with tempfile.TemporaryDirectory() as directory:
        tmp = Path(directory) / 'articles.json'
        tmp.write_text(json.dumps(original, ensure_ascii=False), encoding='utf8')
        with patch(__name__ + '.safe_fetch', side_effect=mock_fetch):
            output = io.StringIO()
            with redirect_stdout(output):
                _, first_additions = update(tmp)
                _, second_additions = update(tmp)
            result = json.loads(tmp.read_text(encoding='utf8'))
        matching = [x for x in result['articles'] if canonical(x.get('url') or '') == known]
        assert first_additions == 1, (first_additions, output.getvalue())
        assert second_additions == 0, (second_additions, output.getvalue())
        assert len(matching) == 1 and matching[0]['kind'] == 'authored'
        assert len(result['articles']) == len(original['articles']) + 1
        assert 'PROBE PASS' in output.getvalue()
    # A known vb.is lead from a news index is a lead only; no GDELT dates
    # are mistaken for publisher publication dates.
    vb_link = ('https://vb.is/frettir/'
               'islenski-hlutabrefamarkadurinn-nalaegt-sogulegu-verdmati/')
    gdelt_mock = json.dumps({'articles': [{'url': vb_link, 'seendate': '20261018T000000Z'},
                                           {'url': 'https://example.org/not-vb'}]}).encode()
    assert discover_gdelt_links(gdelt_mock) == [(vb_link, None)]
    # One GDELT request, regardless of how many terms it covers.
    assert len(gdelt_feed_urls()) == 1
    assert 'CAPE+OR+OMXI15+OR+Brynjar' in gdelt_feed_urls()[0][1]
    # Under rate limiting, retry ONLY after a short explicit Retry-After.
    assert retry_after_seconds(None) is None
    assert retry_after_seconds('4') == 4.0
    assert retry_after_seconds('120') > GDELT_RETRY_MAX_SECONDS
    from email.message import Message
    from urllib.error import HTTPError
    def fake_429(retry_after):
        headers = Message()
        if retry_after is not None:
            headers['Retry-After'] = retry_after
        return HTTPError(gdelt_feed_urls()[0][1], 429, 'Too Many Requests', headers, None)
    with patch(__name__ + '.urlopen', side_effect=[fake_429('1'),
                                                  __import__('io').BytesIO(b'{"articles": []}')]) as u, \
         patch(__name__ + '.time.sleep') as sleep:
        assert get_bytes(gdelt_feed_urls()[0][1]) == b'{"articles": []}'
        assert u.call_count == 2 and sleep.call_count == 1
    with patch(__name__ + '.urlopen', side_effect=fake_429(None)) as u, \
         patch(__name__ + '.time.sleep') as sleep:
        try:
            get_bytes(gdelt_feed_urls()[0][1])
            raise AssertionError('429 without Retry-After should fail safely')
        except HTTPError:
            assert u.call_count == 1 and sleep.call_count == 0
    # Explicit manual addition and duplicate handling never affect production.
    with tempfile.TemporaryDirectory() as directory:
        tmp = Path(directory) / 'articles.json'
        tmp.write_text(json.dumps(original, ensure_ascii=False), encoding='utf-8')
        added = add_manually_reviewed_article(
            tmp, 'https://vb.is/frettir/test-manual-entry/',
            'Prófun á skráningu', '2026-09-15', 'coverage', 'Staðfest umfjöllun')
        duplicate = add_manually_reviewed_article(
            tmp, 'https://vb.is/frettir/test-manual-entry/',
            'Prófun á skráningu', '2026-09-15', 'coverage', 'Staðfest umfjöllun')
        checked = json.loads(tmp.read_text(encoding='utf-8'))
        assert added and not duplicate
        assert len(checked['articles']) == len(original['articles']) + 1
    print('SELF-TEST PASS: one GDELT query, bounded 429 retry, manual-entry '
          'confirmation workflow and duplicate protection.')
    print('SELF-TEST PASS: GDELT index supplies valid publisher URL leads; '
          'no search-index date or attribution is treated as verification.')
    print('SELF-TEST PASS: known article rediscovered from synthetic listing, '
          'correct attribution, archive preserved and no duplicate on second run.')
    print('SELF-TEST LIMIT: mock responses do not prove live publisher/search access.')


if __name__ == '__main__':
    cli = argparse.ArgumentParser(description=__doc__)
    cli.add_argument('--archive', type=Path, default=ARCHIVE_PATH)
    cli.add_argument('--dry-run', action='store_true', help='Display discoveries without writing JSON')
    cli.add_argument('--no-probe', action='store_true', help='Skip known-article diagnostic')
    cli.add_argument('--self-test', action='store_true', help='Test using a TEMPORARY archive, offline')
    cli.add_argument('--add-manual', metavar='URL', help='Curator-verified publisher URL to insert')
    cli.add_argument('--title', help='Title confirmed against publisher')
    cli.add_argument('--date', help='Publication date YYYY-MM-DD confirmed against publisher')
    cli.add_argument('--kind', choices=('authored', 'coverage'), help='Verified authorship or CAPE coverage')
    cli.add_argument('--description', default='', help='Optional short factual description')
    cli.add_argument('--confirm-reviewed', action='store_true',
                     help='Explicitly confirm you personally checked title, date and attribution')
    args = cli.parse_args()
    if args.add_manual:
        if not args.confirm_reviewed or not all((args.title, args.date, args.kind)):
            cli.error('Manual addition requires --title, --date, --kind, and --confirm-reviewed')
        add_manually_reviewed_article(args.archive, args.add_manual,
                                      args.title, args.date, args.kind,
                                      args.description)
    elif args.self_test:
        self_test()
    else:
        # Always verify the parser and archive write logic using a temporary copy.
        # No network access or production file changes occur during this check.
        self_test()
        update(args.archive, dry_run=args.dry_run, run_probe=not args.no_probe)
