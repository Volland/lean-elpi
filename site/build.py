#!/usr/bin/env python3
"""Static site generator for the LeanElpi site (standard library only).

Reads site/content/**/*.md (with a small front matter) and writes docs/ for GitHub Pages.
Usage: python3 site/build.py
"""
import html, re, shutil, sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
SRC = ROOT / "site" / "content"
OUT = ROOT / "docs"
BASE = "/lean-elpi"  # GitHub Pages project path
REPO = "https://github.com/Volland/lean-elpi"

# ---------------------------------------------------------------- markdown
def inline(s: str) -> str:
    codes = []
    def keep(m):
        codes.append("<code>" + html.escape(m.group(1)) + "</code>")
        return f"\x00{len(codes)-1}\x00"
    s = re.sub(r"`([^`]+)`", keep, s)
    s = html.escape(s, quote=False)
    s = re.sub(r"\*\*([^*]+)\*\*", r"<strong>\1</strong>", s)
    s = re.sub(r"(?<![\w*])\*([^*\s][^*]*)\*(?!\w)", r"<em>\1</em>", s)
    def link(m):
        href = m.group(2)
        if href.startswith("/"):
            href = BASE + href
        return f'<a href="{href}">{m.group(1)}</a>'
    s = re.sub(r"\[([^\]]+)\]\(([^)]+)\)", link, s)
    return re.sub(r"\x00(\d+)\x00", lambda m: codes[int(m.group(1))], s)

def md(text: str) -> str:
    out, lines, i = [], text.split("\n"), 0
    para = []
    def flush():
        if para:
            out.append("<p>" + inline(" ".join(para)).replace("\x01 ", "<br>").replace("\x01", "<br>") + "</p>")
            para.clear()
    while i < len(lines):
        ln = lines[i]
        if ln.startswith("```"):
            flush()
            lang = ln[3:].strip()
            i += 1
            buf = []
            while i < len(lines) and not lines[i].startswith("```"):
                buf.append(lines[i]); i += 1
            cls = f' class="language-{lang}"' if lang else ""
            out.append(f"<pre><code{cls}>" + html.escape("\n".join(buf)) + "</code></pre>")
        elif re.match(r"#{1,4} ", ln):
            flush()
            n = len(ln) - len(ln.lstrip("#"))
            title = ln[n + 1:]
            slug = re.sub(r"[^a-z0-9]+", "-", title.lower()).strip("-")
            out.append(f'<h{n} id="{slug}">{inline(title)}</h{n}>')
        elif re.match(r"\s*[-*] ", ln):
            flush()
            items = []
            while i < len(lines) and re.match(r"\s*[-*] ", lines[i]):
                items.append(inline(re.sub(r"^\s*[-*] ", "", lines[i]))); i += 1
            i -= 1
            out.append("<ul>" + "".join(f"<li>{x}</li>" for x in items) + "</ul>")
        elif re.match(r"\d+\. ", ln):
            flush()
            items = []
            while i < len(lines) and re.match(r"\d+\. ", lines[i]):
                items.append(inline(re.sub(r"^\d+\. ", "", lines[i]))); i += 1
            i -= 1
            out.append("<ol>" + "".join(f"<li>{x}</li>" for x in items) + "</ol>")
        elif ln.startswith("> "):
            flush()
            buf = []
            while i < len(lines) and lines[i].startswith("> "):
                buf.append(lines[i][2:]); i += 1
            i -= 1
            out.append("<blockquote>" + md("\n".join(buf)) + "</blockquote>")
        elif ln.startswith("|") and i + 1 < len(lines) and re.match(r"\|[\s:|-]+\|$", lines[i + 1]):
            flush()
            head = [c.strip() for c in ln.strip("|").split("|")]
            i += 2
            rows = []
            while i < len(lines) and lines[i].startswith("|"):
                rows.append([c.strip() for c in lines[i].strip("|").split("|")]); i += 1
            i -= 1
            t = "<table><thead><tr>" + "".join(f"<th>{inline(c)}</th>" for c in head) + "</tr></thead><tbody>"
            for r in rows:
                t += "<tr>" + "".join(f"<td>{inline(c)}</td>" for c in r) + "</tr>"
            out.append(t + "</tbody></table>")
        elif ln.strip() == "":
            flush()
        elif ln.startswith("<"):
            flush(); out.append(ln)
        else:
            para.append(ln.strip() + ("\x01" if ln.endswith("  ") else ""))
        i += 1
    flush()
    return "\n".join(out)

def front(text: str):
    meta = {}
    if text.startswith("---\n"):
        head, _, body = text[4:].partition("\n---\n")
        for l in head.split("\n"):
            k, _, v = l.partition(":")
            meta[k.strip()] = v.strip()
        return meta, body
    return meta, text

# ---------------------------------------------------------------- layout
NAV = [("/", "Home"), ("/book/", "Book"), ("/blog/", "Blog"), (REPO, "GitHub")]

def page(title, body, path, desc="", extra_nav="", article=True):
    nav = "".join(
        f'<a href="{(BASE + h) if h.startswith("/") else h}"{" aria-current=page" if h == path else ""}>{n}</a>'
        for h, n in NAV)
    d = html.escape(desc or "LeanElpi: λProlog (ELPI) implemented natively in Lean 4.")
    return f"""<!doctype html>
<html lang="en">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>{html.escape(title)} · LeanElpi</title>
<meta name="description" content="{d}">
<link rel="stylesheet" href="{BASE}/assets/style.css">
</head>
<body>
<header class="top"><div class="wrap">
<a class="brand" href="{BASE}/">Lean<span>Elpi</span></a>
<nav>{nav}</nav>
</div></header>
<main class="wrap{' prose' if article else ''}">
{extra_nav}
{body}
</main>
<footer><div class="wrap">
<p>LeanElpi is open source under the <a href="{REPO}/blob/main/LICENSE">Apache-2.0 license</a>.</p>
<p><a href="{BASE}/impressum/">Impressum</a> · <a href="{BASE}/datenschutz/">Datenschutz</a> · <a href="{BASE}/agb/">AGB</a></p>
</div></footer>
</body>
</html>
"""

def write(rel, content):
    p = OUT / rel
    p.parent.mkdir(parents=True, exist_ok=True)
    p.write_text(content, encoding="utf-8")

def load(dirname):
    items = []
    for f in sorted((SRC / dirname).glob("*.md")):
        meta, body = front(f.read_text(encoding="utf-8"))
        meta["slug"] = f.stem
        items.append((meta, body))
    return items

def main():
    if OUT.exists():
        shutil.rmtree(OUT)
    OUT.mkdir()
    shutil.copytree(ROOT / "site" / "assets", OUT / "assets")
    (OUT / ".nojekyll").write_text("")

    # home
    home = (SRC / "home.html").read_text(encoding="utf-8").replace("{{BASE}}", BASE)
    write("index.html", page("λProlog in Lean 4", home, "/", article=False,
          desc="LeanElpi is a native Lean 4 implementation of ELPI (λProlog) with kernel-checked proof search."))

    # book
    chapters = sorted(load("book"), key=lambda x: int(x[0].get("order", "99")))
    def toc(cur):
        li = "".join(
            f'<li><a href="{BASE}/book/{m["slug"]}/"{" aria-current=page" if m["slug"] == cur else ""}>{html.escape(m["title"])}</a></li>'
            for m, _ in chapters)
        return f'<aside class="toc"><strong>The book</strong><ol>{li}</ol></aside>'
    cards = "".join(
        f'<li><a href="{BASE}/book/{m["slug"]}/"><strong>{html.escape(m["title"])}</strong></a><br>{html.escape(m.get("summary",""))}</li>'
        for m, _ in chapters)
    write("book/index.html", page("The λProlog book",
        f"<h1>λProlog and LeanElpi: a short book</h1><p>A hands-on introduction to λProlog, to its implementation in Lean 4, and to why higher-order logic matters for neuro-symbolic systems. Read it in order, or jump to the chapter you need.</p><ol class=chapters>{cards}</ol>",
        "/book/", desc="A short book on λProlog, ELPI, and LeanElpi."))
    for n, (m, body) in enumerate(chapters):
        prev = chapters[n - 1][0] if n else None
        nxt = chapters[n + 1][0] if n + 1 < len(chapters) else None
        pn = '<nav class="pager">'
        pn += f'<a href="{BASE}/book/{prev["slug"]}/">← {html.escape(prev["title"])}</a>' if prev else "<span></span>"
        pn += f'<a href="{BASE}/book/{nxt["slug"]}/">{html.escape(nxt["title"])} →</a>' if nxt else "<span></span>"
        pn += "</nav>"
        write(f"book/{m['slug']}/index.html", page(m["title"],
            f"<article>{md(body)}</article>{pn}", "/book/", desc=m.get("summary", ""), extra_nav=toc(m["slug"])))

    # blog
    posts = sorted(load("blog"), key=lambda x: x[0].get("date", ""), reverse=True)
    lst = "".join(
        f'<li><a href="{BASE}/blog/{m["slug"]}/"><strong>{html.escape(m["title"])}</strong></a><br><time>{m.get("date","")}</time> · {html.escape(m.get("summary",""))}</li>'
        for m, _ in posts)
    write("blog/index.html", page("Blog", f"<h1>Blog</h1><ul class=posts>{lst}</ul>", "/blog/",
          desc="Articles about LeanElpi."))
    for m, body in posts:
        write(f"blog/{m['slug']}/index.html", page(m["title"],
            f"<article><p class=meta><time>{m.get('date','')}</time> · {html.escape(m.get('author',''))}</p>{md(body)}</article>",
            "/blog/", desc=m.get("summary", "")))

    # legal
    for slug in ("impressum", "datenschutz", "agb"):
        m, body = front((SRC / f"{slug}.md").read_text(encoding="utf-8"))
        write(f"{slug}/index.html", page(m["title"], f"<article>{md(body)}</article>", f"/{slug}/"))
    write("404.html", page("Not found", "<h1>Page not found</h1><p><a href=\"" + BASE + "/\">Back to the home page</a></p>", "/"))
    print("built", sum(1 for _ in OUT.rglob("*.html")), "pages")

if __name__ == "__main__":
    sys.exit(main())
