#!/usr/bin/env python3
"""Conservative article discovery for Iceland Market Monitor.

Sources:
* The public Innherji/Vísir opinion listing.
* The public Viðskiptablaðið RSS feed.

Only publish articles with a verified Brynjar Örn Ólafsson byline, or
third-party pieces whose own body explicitly connects Brynjar to CAPE.
Avoid guessing article dates, titles or authors; preserve the hand-curated archive.
"""
from __future__ import annotations

import argparse
from collections import Counter
from datetime import datetime, timezone
from email.utils import parsedate_to_datetime
from html import unescape
import json
from pathlib import Path
import re
import sys
import time
from urllib.parse import urljoin, urlsplit, urlunsplit
from urllib.request import Request, urlopen
import xml.etree.ElementTree as ET

from bs4 import BeautifulSoup

ARCHIVE_PATH = Path(__file__).with_name('articles.json')
VB_RSS = 'https://www.vb.is/rss/'
VISIR_PAGES = ['https://www.visir.is/f/umraedan', 'https://www.visir.is/f/umraedan/1']
AUTHOR = 'brynjar orn olafsson'
HEADLINE_TERMS = ('cape', 'omxi', 'úrvalsvísit', 'hlutabréf', 'verðlagning', 'eignaverð', 'brynjar')
MONTHS = {'janúar':1,'febrúar':2,'mars':3,'apríl':4,'maí':5,'júní':6,'júlí':7,'ágúst':8,
          'september':9,'október':10,'nóvember':11,'desember':12}


def normalized(text: str) -> str:
    import unicodedata
    text = unicodedata.normalize('NFD', (text or '').replace('\u00ad','').replace('\u200b',''))
    return ''.join(c for c in text if not unicodedata.combining(c)).casefold()


def canonical(url: str) -> str:
    split = urlsplit(url)
    return urlunsplit((split.scheme.lower(), split.netloc.lower().removeprefix('www.'), split.path.rstrip('/'), '', ''))


def get_bytes(url: str) -> bytes:
    request = Request(url,headers={
        'User-Agent': 'IcelandMarketMonitor-ArticleFeed/0.1 (+https://brynjarolafsson.github.io/iceland-market-monitor/)',
        'Accept': 'text/html, application/rss+xml, application/xml;q=0.9, */*;q=0.5',
    })
    with urlopen(request,timeout=25) as response:
        return response.read(2_500_000)


def safe_fetch(url: str) -> bytes | None:
    try: return get_bytes(url)
    except Exception as exc:
        print(f'WARNING: Could not retrieve {url}: {exc}',file=sys.stderr)
        return None


def discover_visir_links(page_html: bytes, base_url: str) -> list[str]:
    """Select links whose nearby article-card text actually includes the author."""
    soup=BeautifulSoup(page_html, 'html.parser')
    links=[]
    for a in soup.select('a[href*="/g/"]'):
        href=urljoin(base_url,a.get('href',''))
        if not href.startswith(('https://www.visir.is/g/','http://www.visir.is/g/')):
            continue
        current=a
        matched=False
        for _ in range(5):
            current=current.parent
            if current is None:break
            # Never borrow the author's name from neighbouring article cards.
            neighbouring={a.get('href') for a in current.select('a[href*="/g/"]')}
            if len(neighbouring)>1:break
            text=current.get_text(' ',strip=True)
            if len(text)>1100:break
            if AUTHOR in normalized(text):
                matched=True;break
        if matched: links.append(href)
    return list(dict.fromkeys(links))


def discover_vb_links(feed_xml: bytes) -> list[tuple[str,str|None]]:
    """RSS is used for discovery, not as proof of an article's author."""
    root=ET.fromstring(feed_xml)
    records=[]
    for item in root.findall('.//item')[:100]:
        link=(item.findtext('link') or '').strip()
        title=(item.findtext('title') or '').strip()
        description=(item.findtext('description') or '').strip()
        if not link.startswith(('https://','http://')):continue
        contents=normalized(unescape(title + ' ' + BeautifulSoup(description,'html.parser').get_text(' ',strip=True)))
        if any(normalized(term) in contents for term in HEADLINE_TERMS):
            records.append((link,item.findtext('pubDate')))
    return list(dict.fromkeys(records))


def first_meta(soup: BeautifulSoup, names: tuple[str,...]) -> str:
    for name in names:
        x=soup.select_one(f'meta[property="{name}"]') or soup.select_one(f'meta[name="{name}"]')
        if x and x.get('content'):return x['content'].strip()
    return ''


def body_text(soup:BeautifulSoup) -> str:
    doc=soup.select_one('article') or soup.select_one('main') or soup.body or soup
    # Clone to avoid mutating metadata/content queries.
    soup2=BeautifulSoup(str(doc),'html.parser')
    for unwanted in soup2.select('nav, aside, footer, script, style, header, [class*="related"], [class*="Related"]'):
        unwanted.decompose()
    return soup2.get_text(' ',strip=True)


def published_date(soup:BeautifulSoup, fallback_rss_date:str|None) -> str|None:
    options=[first_meta(soup,('article:published_time','datePublished','pubdate','date'))]
    when=soup.find('time',attrs={'datetime':True})
    if when:options.append(when.get('datetime',''))
    if fallback_rss_date:options.append(fallback_rss_date)
    for opt in options:
        if not opt:continue
        try:
            parsed=datetime.fromisoformat(opt.replace('Z','+00:00'))
            return parsed.date().isoformat()
        except (ValueError,TypeError):pass
        try:
            parsed=parsedate_to_datetime(opt)
            return parsed.date().isoformat()
        except (ValueError,TypeError,IndexError):pass
    # Icelandic byline printed near the headline, not a guessed publication date.
    txt=(soup.get_text(' ',strip=True)[:1600])
    match=re.search(r'(\d{1,2})\.\s*('+ '|'.join(MONTHS) +r')\s+(20\d{2})',txt,re.I)
    if match:
        day,month,year=match.groups()
        try:return datetime(int(year),MONTHS[month.lower()],int(day)).date().isoformat()
        except ValueError:pass
    return None


def topic_of(title:str) -> str:
    t=normalized(title)
    if any(w in t for w in ('innherja',' mar ','eftirlit','regluverk','tilboðabreyting','tilbodabreyting')):return 'Regluverk og markaðir'
    if any(w in t for w in ('cape','hlutabref','omxi','hagnad','eignaverd','kaupholl','urvalsvisit')):return 'Hlutabréf og eignaverð'
    if any(w in t for w in ('skuldabref','vaxt','vext','verðtrygg','verdtrygg','rikisbr','rikisb')):return 'Skuldabréf og vextir'
    return 'Þjóðhagfræði'


def describe_candidate(url:str, html_bytes:bytes, source:str, rss_date:str|None=None) -> dict | None:
    soup=BeautifulSoup(html_bytes,'html.parser')
    title=first_meta(soup,('og:title','twitter:title'))
    if not title:
        heading=soup.find('h1')
        title=heading.get_text(' ',strip=True) if heading else ''
    title=re.sub(r'\s+[-|]\s+(Innherji|Vísir|Viðskiptablaðið)\s*$','',title).strip()
    if not title:return None
    date=published_date(soup,rss_date)
    if not date:return None
    if date > datetime.now(timezone.utc).date().isoformat():return None
    raw=body_text(soup)
    content=normalized(raw)
    byline=normalized(first_meta(soup,('author','article:author','byl')))
    # Vísir often prints "Brynjar Örn Ólafsson skrifar ..." rather than author metadata.
    byline_in_intro=bool(re.search(r'brynjar orn olafsson\s+skrifar',normalized(soup.get_text(' ',strip=True)[:1500])))
    is_authored=(AUTHOR in byline) or byline_in_intro
    if is_authored:
        kind='authored'
    else:
        # A CAPE citation must be explicit in the actual article body, not only the footer.
        matches=[m.start() for m in re.finditer(AUTHOR,content)]
        capes=[m.start() for m in re.finditer('cape',content)]
        if not matches or not capes or min(abs(a-c) for a in matches for c in capes)>850:
            return None
        kind='coverage'
    desc=first_meta(soup,('og:description','description'))
    desc=re.sub(r'\s+',' ',BeautifulSoup(desc,'html.parser').get_text(' ',strip=True))[:250]
    if not desc:
        desc='Fjölmiðlaumfjöllun sem vísar í CAPE-gögn.' if kind=='coverage' else 'Ný grein eftir Brynjar Örn Ólafsson.'
    return {'title':title,'date':date,'year':int(date[:4]),'source':source,'kind':kind,
            'topic': 'Hlutabréf og eignaverð' if kind=='coverage' else topic_of(title),
            'url':canonical(url).replace('://visir.is','://www.visir.is'),
            'description':desc,'extra_links':[]}


def update(archive_path:Path=ARCHIVE_PATH) -> tuple[int,int]:
    data=json.loads(archive_path.read_text(encoding='utf8'))
    old=data['articles']
    known={canonical(x['url']) for x in old if x.get('url')}
    candidates:list[tuple[str,str,str|None]]=[]
    checked=0
    for page in VISIR_PAGES:
        raw=safe_fetch(page)
        if raw is None:continue
        checked+=1
        for url in discover_visir_links(raw,page): candidates.append((url,'Innherji',None))
    rss=safe_fetch(VB_RSS)
    if rss is not None:
        checked+=1
        try:
            for url,rss_date in discover_vb_links(rss):
                candidates.append((url,'Viðskiptablaðið',rss_date))
        except ET.ParseError as error:
            print(f'WARNING: Could not parse VB RSS: {error}',file=sys.stderr)
    if not checked:
        raise RuntimeError('All article discovery sources unavailable; no changes written')
    discovered=list(dict.fromkeys((canonical(u),source,date) for u,source,date in candidates))
    added=[]
    for url,source,rss_date in discovered:
        if url in known:continue
        raw=safe_fetch(url)
        if raw is None:continue
        record=describe_candidate(url,raw,source,rss_date)
        if record:
            new_key=canonical(record['url'])
            if new_key not in known:
                known.add(new_key)
                old.append(record)
                added.append(record)
    old.sort(key=lambda x:(x.get('date') or f"{x['year']}-01-01",x.get('title','')),reverse=True)
    print(f'Sources retrieved: {checked}; URLs screened: {len(discovered)}; new verified entries: {len(added)}')
    for r in added:print(f"  {r['date']} | {r['kind']} | {r['source']} | {r['title']}")
    if added:
        temp=archive_path.with_suffix('.json.tmp')
        temp.write_text(json.dumps(data,indent=2,ensure_ascii=False)+'\n',encoding='utf8')
        temp.replace(archive_path)
    return len(discovered),len(added)


if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--archive',type=Path,default=ARCHIVE_PATH)
    args=parser.parse_args()
    update(args.archive)
