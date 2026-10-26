# Generates docs/banner-light.svg and docs/banner-dark.svg (README banner):
# one theorem, four objects, how each is found and what it survives.
# Run from the repository root: python3 docs/banner.py
# Values are real (Nat.add_zero, Lean v4.35.0, CA scheme 1). After regenerating,
# bump the ?v= query on the README's two image URLs (GitHub caches images by URL).
PAL = {
 'light': dict(fill='#f6f8fa', stroke='#afb8c4', text='#1f2328', muted='#6e7781', accent='#0969da', edge='#8c959f'),
 'dark':  dict(fill='#161b22', stroke='#3d444d', text='#e6edf3', muted='#9198a1', accent='#4493f8', edge='#6e7681'),
}
SANS = "ui-sans-serif,-apple-system,'Segoe UI',Helvetica,Arial,sans-serif"
MONO = "ui-monospace,SFMono-Regular,Menlo,Consolas,monospace"
W, H = 1200, 296

TILES = [  # kicker, main (mono), id line (mono), found by, survives, emphasised
  ('NAME', 'Nat.add_zero', 'a binding in a namespace', 'its namespace', 'until renamed', False),
  ('STATEMENT', '∀ n : Nat, n + 0 = n', 'stmt ByKFv4nqHrcs…', 'computing it from the proposition', 'renames, moves, re-proving', True),
  ('LEAN PROOF', ':= rfl', 'Init/Core.lean:747', 'the repository holding it', 'nothing beyond its text', False),
  ('PROOF TERM', 'fun n => rfl', 'decl CRBaL3yvth9g…', 'asking the network', 'renames only', False),
]
WIDTHS = [190, 300, 190, 210]
GAP = 90
X0 = (W - sum(WIDTHS) - GAP * 3) / 2
TY, TH = 64, 104

def arrow(x1, x2, y, label, p, left=False):
    a, b = (x2, x1) if left else (x1, x2)
    s = f'<line x1="{a}" y1="{y}" x2="{b}" y2="{y}" stroke="{p["edge"]}" stroke-width="1.6" marker-end="url(#arr)"/>\n'
    s += f'<text x="{(x1+x2)/2}" y="{y-9}" text-anchor="middle" font-family="{SANS}" font-size="12.5" fill="{p["muted"]}">{label}</text>\n'
    return s

def banner(p):
    o = f'<svg xmlns="http://www.w3.org/2000/svg" width="{W}" height="{H}" viewBox="0 0 {W} {H}" role="img" aria-label="CA: one theorem, four objects. Its name is found by asking a namespace and survives until renamed; its statement is found by computing it from the proposition and survives renames, moves and re-proving; its Lean proof is found in a repository; its proof term is a cache found by asking the network for witnesses.">\n'
    o += f'<defs><marker id="arr" viewBox="0 0 10 10" refX="9" refY="5" markerWidth="8" markerHeight="8" orient="auto-start-reverse"><path d="M0,0 L10,5 L0,10 z" fill="{p["edge"]}"/></marker></defs>\n'
    o += f'<text x="{X0}" y="34" font-family="{SANS}" font-size="15" fill="{p["muted"]}" letter-spacing="0.8">ONE THEOREM, FOUR OBJECTS — HOW EACH IS FOUND, AND WHAT IT SURVIVES</text>\n'
    o += f'<text x="{W-X0}" y="34" text-anchor="end" font-family="{MONO}" font-size="18" font-weight="600" fill="{p["text"]}">CA</text>\n'
    xs = []
    x = X0
    for w in WIDTHS:
        xs.append(x); x += w + GAP
    for (kick, main, idl, found, surv, emph), x, w in zip(TILES, xs, WIDTHS):
        stroke = p['accent'] if emph else p['stroke']
        sw = 2.4 if emph else 1.4
        o += f'<rect x="{x}" y="{TY}" width="{w}" height="{TH}" rx="10" fill="{p["fill"]}" stroke="{stroke}" stroke-width="{sw}"/>\n'
        cx = x + w / 2
        o += f'<text x="{cx}" y="{TY+24}" text-anchor="middle" font-family="{SANS}" font-size="12.5" fill="{p["muted"]}" letter-spacing="0.8">{kick}</text>\n'
        o += f'<text x="{cx}" y="{TY+56}" text-anchor="middle" font-family="{MONO}" font-size="17" fill="{p["text"]}">{main}</text>\n'
        idcol = p['accent'] if idl.startswith(('stmt', 'decl')) else p['muted']
        idfont = MONO if idl.startswith(('stmt', 'decl')) else SANS
        o += f'<text x="{cx}" y="{TY+86}" text-anchor="middle" font-family="{idfont}" font-size="13.5" fill="{idcol}">{idl}</text>\n'
        o += f'<text x="{cx}" y="{TY+TH+36}" text-anchor="middle" font-family="{SANS}" font-size="14" fill="{p["text"]}"><tspan fill="{p["muted"]}">found by</tspan><tspan dx="6">{found}</tspan></text>\n'
        o += f'<text x="{cx}" y="{TY+TH+60}" text-anchor="middle" font-family="{SANS}" font-size="14" fill="{p["text"]}"><tspan fill="{p["muted"]}">survives</tspan><tspan dx="6">{surv}</tspan></text>\n'
    ay = TY + TH / 2
    o += arrow(xs[0] + WIDTHS[0] + 4, xs[1] - 4, ay, 'names', p)
    o += arrow(xs[1] + WIDTHS[1] + 4, xs[2] - 4, ay, 'proves', p, left=True)
    o += arrow(xs[2] + WIDTHS[2] + 4, xs[3] - 4, ay, 'elaborates to', p)
    o += f'<text x="{W/2}" y="{H-20}" text-anchor="middle" font-family="{SANS}" font-size="14.5" fill="{p["muted"]}">cite the statement: anyone can compute it, and nothing a proof does can change it · proofs are interchangeable witnesses · terms are caches</text>\n'
    o += '</svg>\n'
    return o

for theme, p in PAL.items():
    open(f'docs/banner-{theme}.svg', 'w').write(banner(p))
print("banner written")
