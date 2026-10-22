# Generates docs/figure-stmt-dag-light.svg and -dark.svg, the figure of docs/worked-example.md:
# how Nat.add_zero's stmt embeds the ids of the constants its statement mentions.
# Run from the repository root: python3 docs/figure-stmt-dag.py
# The ids on the tiles are real (Lean v4.35.0, scheme 1); regenerate them if the scheme changes.
PAL = {
 'light': dict(fill='#f6f8fa', stroke='#afb8c4', text='#1f2328', muted='#6e7781', accent='#0969da', dash='#8c959f', edge='#8c959f'),
 'dark':  dict(fill='#161b22', stroke='#3d444d', text='#e6edf3', muted='#9198a1', accent='#4493f8', dash='#6e7681', edge='#6e7681'),
}
SANS = "ui-sans-serif,-apple-system,'Segoe UI',Helvetica,Arial,sans-serif"
MONO = "ui-monospace,SFMono-Regular,Menlo,Consolas,monospace"
W, H = 1200, 400

def tile(x, y, w, h, name, addr, p, dashed=False, name_fs=17, addr_fs=13.5):
    stroke = p['dash'] if dashed else p['stroke']
    da = ' stroke-dasharray="7 6"' if dashed else ''
    s = f'<rect x="{x}" y="{y}" width="{w}" height="{h}" rx="10" fill="{p["fill"]}" stroke="{stroke}" stroke-width="1.4"{da}/>\n'
    col = p['muted'] if dashed else p['text']
    s += f'<text x="{x+w/2}" y="{y+26}" text-anchor="middle" font-family="{SANS}" font-size="{name_fs}" fill="{col}">{name}</text>\n'
    if addr:
        acol = p['muted'] if dashed else p['accent']
        s += f'<text x="{x+w/2}" y="{y+h-14}" text-anchor="middle" font-family="{MONO}" font-size="{addr_fs}" fill="{acol}">{addr}</text>\n'
    return s

def edge(x1, y1, x2, y2, p):
    return f'<path d="M{x1},{y1} C{x1},{(y1+y2)/2} {x2},{(y1+y2)/2} {x2},{y2}" fill="none" stroke="{p["edge"]}" stroke-width="1.6" marker-end="url(#arr)"/>\n'

def hedge(x1, y1, x2, y2, p):
    return f'<path d="M{x1},{y1} C{(x1+x2)/2},{y1} {(x1+x2)/2},{y2} {x2},{y2}" fill="none" stroke="{p["edge"]}" stroke-width="1.6" marker-end="url(#arr)"/>\n'

def banner(p):
    o = f'<svg xmlns="http://www.w3.org/2000/svg" width="{W}" height="{H}" viewBox="0 0 {W} {H}" role="img" aria-label="CA: an address is made of the shape of a statement and the addresses of what it mentions; the proof is not part of it">\n'
    o += f'<defs><marker id="arr" viewBox="0 0 10 10" refX="9" refY="5" markerWidth="8" markerHeight="8" orient="auto-start-reverse"><path d="M0,0 L10,5 L0,10 z" fill="{p["edge"]}"/></marker></defs>\n'
    o += f'<text x="40" y="36" font-family="{SANS}" font-size="15" fill="{p["muted"]}" letter-spacing="0.8">AN ADDRESS IS MADE OF THE SHAPE OF A STATEMENT AND THE ADDRESSES OF WHAT IT MENTIONS</text>\n'
    o += f'<text x="{W-40}" y="36" text-anchor="end" font-family="{MONO}" font-size="18" font-weight="600" fill="{p["text"]}">CA</text>\n'
    # top row: Nat | theorem | proof
    ty, th = 62, 70
    o += tile(40, ty, 150, th, 'Nat', '9bUmPmuYBLg…', p)
    tx, tw = 218, 560
    o += tile(tx, ty, tw, th, 'theorem : ∀ n : Nat, n + 0 = n', 'stmt ByKFv4nqHrcsFWuBFd7ihUXKFNEdMvFdMvjW7n8XE3nn', p, addr_fs=13)
    o += hedge(191, ty+th/2, tx-1, ty+th/2, p)
    px, pw = 806, 354
    o += tile(px, ty, pw, th, 'proof', 'fun n => Nat.add_zero n', p, dashed=True)
    o += f'<text x="{px+pw/2}" y="{ty+th+22}" text-anchor="middle" font-family="{SANS}" font-size="14" fill="{p["muted"]}">not part of the address</text>\n'
    # middle row: the other six constants the elaborated statement mentions
    mw, mh, my, gap = 172, 62, 196, 14
    xs = [40 + i*(mw+gap) for i in range(6)]
    mids = list(zip(xs, ['Eq', 'HAdd.hAdd', 'instHAdd', 'instAddNat', 'OfNat.ofNat', 'instOfNatNat'],
                        ['CsCMj6owGLa…', '3H2JnCKuEaT…', '6rEFXi3hyDW…', '33sftyMqxjE…', 'AkiSexvWpb4…', 'Fsqscbcf7WG…']))
    for x, n, a in mids:
        o += tile(x, my, mw, mh, n, a, p)
    for i, (x, _, _) in enumerate(mids):
        ex = tx + 40 + i*(tw-80)/5
        o += edge(x+mw/2, my, ex, ty+th+1, p)
    # bottom row: values of the two instances (a definition's id includes its value)
    by = 310
    o += tile(xs[2], by, mw, mh, 'Add.add', 'AobaYk1sJ4R…', p)
    o += tile(xs[3], by, mw, mh, 'Nat.add', 'Hi9pXw413qN…', p)
    o += edge(xs[2]+mw/2, by, xs[2]+mw/2, my+mh+1, p)
    o += edge(xs[3]+mw/2, by, xs[3]+mw/2, my+mh+1, p)
    o += f'<text x="{xs[4]+8}" y="{by+38}" font-family="{SANS}" font-size="14" fill="{p["muted"]}">← a definition\'s id includes its value</text>\n'
    o += f'<text x="40" y="{H-14}" font-family="{SANS}" font-size="14" fill="{p["muted"]}">the statement as elaborated, no unfolding, with each constant replaced by its id · a theorem\'s id never includes its proof · names never enter</text>\n'
    o += '</svg>\n'
    return o

for theme, p in PAL.items():
    open(f'docs/figure-stmt-dag-{theme}.svg', 'w').write(banner(p))
print("written")
