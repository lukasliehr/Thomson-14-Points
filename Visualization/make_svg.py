#!/usr/bin/env python3
"""Writes bicapped-hexagonal-antiprism.svg: the minimizer for 14 points, rotating about its axis.

    python3 Visualization/make_svg.py

The picture is an animated SVG without scripts. The configuration is mapped to itself by a rotation
of 60 degrees about its axis, so the animation only stores a turn of 60 degrees and repeats it: every
point then stands where its neighbour stood, and the picture is the same. Between the stored
positions the browser interpolates. The program uses the standard library of Python only.
"""
import math
import os

# ---- the configuration ----------------------------------------------------------------------------
H = 0.45536779516246300350924502372107445741075259468695   # the optimal height
ENERGY = "69.306"                                             # the minimal energy, rounded
R_RING = math.sqrt(1 - H * H)

NORTH, SOUTH = 0, 1
UP = [2 + k for k in range(6)]          # the hexagon at height h
LOW = [8 + k for k in range(6)]         # the hexagon at height -h, rotated by 30 degrees


def vertices(theta):
    """The 14 points after a rotation by `theta` about the axis."""
    pts = [(0.0, 0.0, 1.0), (0.0, 0.0, -1.0)]
    for k in range(6):
        a = theta + k * math.pi / 3
        pts.append((R_RING * math.cos(a), R_RING * math.sin(a), H))
    for k in range(6):
        a = theta + k * math.pi / 3 + math.pi / 6
        pts.append((R_RING * math.cos(a), R_RING * math.sin(a), -H))
    return pts


FACES = []                               # the 24 triangles of the convex hull, outward orientation
for k in range(6):
    u0, u1, l0, l1 = UP[k], UP[(k + 1) % 6], LOW[k], LOW[(k + 1) % 6]
    FACES += [(NORTH, u0, u1), (u0, l0, u1), (u1, l0, l1), (SOUTH, l1, l0)]

EDGES = []                               # (i, j, kind): the 36 edges
for k in range(6):
    u0, u1, l0, l1 = UP[k], UP[(k + 1) % 6], LOW[k], LOW[(k + 1) % 6]
    EDGES += [(u0, u1, "up"), (l0, l1, "low"), (NORTH, u0, "side"), (SOUTH, l0, "side"),
              (u0, l0, "side"), (u1, l0, "side")]

# ---- the picture ----------------------------------------------------------------------------------
W, HEIGHT = 840, 440
CX, CY, RAD = 228, 212, 160              # the centre and the radius of the sphere in the picture
DIST = 6.0                               # the distance of the camera from the centre
ELEV = math.radians(19)                  # its elevation
START = math.radians(14)                 # the rotation of the first picture
BALL = 0.058                             # the radius of a point, in units of the sphere
STEPS = 12                               # stored positions per 60 degrees: every 5 degrees
DUR = "7s"                               # the time of a turn of 60 degrees

PAGE, INK, INK2, MUTED, GOOD = "#f9f9f7", "#0b0b0b", "#52514e", "#6f6e69", "#008300"
BLUE, GREEN, NEUTRAL = "#2a78d6", "#149a6b", "#7d7c76"
EDGE, FACE, TINT, RIM = "#6f6e68", "#6a7f9e", "#8794a8", "#5b6b84"
COLOR = {NORTH: NEUTRAL, SOUTH: NEUTRAL, **{i: BLUE for i in UP}, **{i: GREEN for i in LOW}}
GRAD = {NEUTRAL: "n", BLUE: "b", GREEN: "g"}

FOCAL = RAD * math.sqrt(DIST * DIST - 1)                     # the sphere has the radius RAD
CAM = (math.cos(ELEV), 0.0, math.sin(ELEV))                  # the direction to the camera
RIGHT = (0.0, 1.0, 0.0)
UPV = (-math.sin(ELEV), 0.0, math.cos(ELEV))
LIGHT = (0.45, -0.55, 0.70)                                  # the direction to the light
LIGHT = tuple(c / math.sqrt(sum(x * x for x in LIGHT)) for c in LIGHT)


def dot(a, b):
    return a[0] * b[0] + a[1] * b[1] + a[2] * b[2]


def sub(a, b):
    return (a[0] - b[0], a[1] - b[1], a[2] - b[2])


def cross(a, b):
    return (a[1] * b[2] - a[2] * b[1], a[2] * b[0] - a[0] * b[2], a[0] * b[1] - a[1] * b[0])


def unit(a):
    n = math.sqrt(dot(a, a))
    return (a[0] / n, a[1] / n, a[2] / n)


def smooth(x, lo, hi):
    t = min(1.0, max(0.0, (x - lo) / (hi - lo)))
    return t * t * (3 - 2 * t)


def project(p):
    """The place of a point in the picture, and the scale of lengths at this point."""
    s = FOCAL / (DIST - dot(p, CAM))
    return CX + s * dot(p, RIGHT), CY - s * dot(p, UPV), s


def frame(theta):
    """Everything that the picture shows for one rotation."""
    pts = vertices(theta)
    eye = tuple(DIST * c for c in CAM)
    xy = [project(p) for p in pts]
    # a point is in front if it lies on the side of the sphere that the camera sees
    front = [smooth(dot(p, CAM) - 1 / DIST, -0.035, 0.035) for p in pts]
    facing, shade = [], []
    for a, b, c in FACES:
        n = unit(cross(sub(pts[b], pts[a]), sub(pts[c], pts[a])))
        assert all(dot(n, sub(q, pts[a])) < 1e-9 for q in pts), "the faces are not the convex hull"
        facing.append(dot(n, unit(sub(eye, pts[a]))))
        shade.append(max(0.0, dot(n, LIGHT)))
    return pts, xy, front, facing, shade


FRAMES = [frame(START + j * (math.pi / 3) / STEPS) for j in range(STEPS + 1)]


def num(x, digits=1):
    s = f"{x:.{digits}f}"
    if "." in s:
        s = s.rstrip("0").rstrip(".")
    return "0" if s in ("-0", "") else s


def animate(attr, values):
    """An attribute with its first value, and the animation if the value changes."""
    if all(v == values[0] for v in values):
        return f' {attr}="{values[0]}"', ""
    return (f' {attr}="{values[0]}"',
            f'<animate attributeName="{attr}" dur="{DUR}" repeatCount="indefinite" values="{";".join(values)}"/>')


def element(tag, static, animated):
    attrs, anims = "", ""
    for attr, values in animated:
        a, b = animate(attr, values)
        attrs += a
        anims += b
    return f"<{tag}{static}{attrs}>{anims}</{tag}>" if anims else f"<{tag}{static}{attrs}/>"


def mix(color, other, t):
    a = [int(color[i:i + 2], 16) for i in (1, 3, 5)]
    b = [int(other[i:i + 2], 16) for i in (1, 3, 5)]
    return "#" + "".join(f"{round(x + (y - x) * t):02x}" for x, y in zip(a, b))


def faces():
    out = []
    for f, (a, b, c) in enumerate(FACES):
        pts = [" ".join(f"{num(fr[1][i][0])},{num(fr[1][i][1])}" for i in (a, b, c)) for fr in FRAMES]
        # a face that looks at the camera is shaded by the light, a face on the far side is faint
        op = [num(0.035 + smooth(fr[3][f], -0.04, 0.04) * (0.025 + 0.095 * fr[4][f]), 3) for fr in FRAMES]
        out.append(element("polygon", "", [("points", pts), ("fill-opacity", op)]))
    return out


def edges():
    out = []
    adjacent = {}
    for f, tri in enumerate(FACES):
        for i in range(3):
            adjacent.setdefault(frozenset((tri[i], tri[(i + 1) % 3])), []).append(f)
    for a, b, kind in EDGES:
        fa = adjacent[frozenset((a, b))]
        assert len(fa) == 2
        ds, ops = [], []
        for pts, xy, front, facing, shade in FRAMES:
            (x1, y1, s1), (x2, y2, s2) = xy[a], xy[b]
            # the edge ends at the surfaces of its two points
            length = math.hypot(x2 - x1, y2 - y1)
            ux, uy = (x2 - x1) / length, (y2 - y1) / length
            t1, t2 = BALL * s1 * 0.92, BALL * s2 * 0.92
            ds.append(f"M{num(x1 + ux * t1)} {num(y1 + uy * t1)}L{num(x2 - ux * t2)} {num(y2 - uy * t2)}")
            # an edge is in front if one of its two faces looks at the camera
            vis = smooth(max(facing[fa[0]], facing[fa[1]]), -0.04, 0.04)
            ops.append(num(0.22 + 0.7 * vis, 2))
        cls = {"up": ' class="u"', "low": ' class="l"', "side": ""}[kind]
        out.append(element("path", cls, [("d", ds), ("stroke-opacity", ops)]))
    return out


def points(layer):
    """The points of the far side (`layer` 0) or of the near side (`layer` 1).

    A point of the far side is drawn in a paler colour, as if seen through haze, and it is opaque. While
    a point passes the outline of the sphere, its near copy fades in over its far copy."""
    out = []
    for i in range(14):
        near = [fr[2][i] for fr in FRAMES]
        if layer:
            op = [num(v, 2) for v in near]
        else:
            op = ["1" if v < 0.98 else "0" for v in near]
        if all(v == "0" for v in op):
            continue
        cx = [num(fr[1][i][0]) for fr in FRAMES]
        cy = [num(fr[1][i][1]) for fr in FRAMES]
        r = [num(BALL * fr[1][i][2], 2) for fr in FRAMES]
        grad = GRAD[COLOR[i]] + ("" if layer else "f")
        out.append(element("circle", f' fill="url(#{grad})"', [("cx", cx), ("cy", cy), ("r", r), ("opacity", op)]))
    return out


HAZE = "#e7e8ea"                         # the colour towards which the far side fades


def gradient(name, color, haze=0.0):
    stops = [(0, mix(color, "#ffffff", 0.62)), (.45, color), (1, mix(color, "#000000", 0.38))]
    return (f'<radialGradient id="{name}" cx=".34" cy=".3" r=".8">'
            + "".join(f'<stop offset="{num(o, 2)}" stop-color="{mix(c, HAZE, haze)}"/>' for o, c in stops)
            + "</radialGradient>")


TX = 506                                 # the left edge of the text


def legend(y, color, text):
    return (f'<circle cx="{TX + 6}" cy="{y - 5}" r="5.5" fill="url(#{GRAD[color]})"/>'
            f'<text x="{TX + 23}" y="{y}">{text}</text>')


def check_loop():
    """After 60 degrees the picture is the first picture: every point stands where its neighbour stood."""
    first, last = FRAMES[0], FRAMES[-1]
    def key(fr, i):
        return (COLOR[i], round(fr[1][i][0], 6), round(fr[1][i][1], 6), round(fr[2][i], 6))
    assert sorted(key(first, i) for i in range(14)) == sorted(key(last, i) for i in range(14))
    def fkey(fr, f):
        return (tuple(sorted((round(fr[1][i][0], 6), round(fr[1][i][1], 6)) for i in FACES[f])),
                round(fr[3][f], 6), round(fr[4][f], 6))
    assert sorted(fkey(first, f) for f in range(24)) == sorted(fkey(last, f) for f in range(24))


def svg():
    font = "Inter,system-ui,-apple-system,'Segoe UI',Helvetica,Arial,sans-serif"
    h = '<tspan font-style="italic" font-family="Georgia,\'Times New Roman\',serif">h</tspan>'
    parts = [
        f'<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 {W} {HEIGHT}" width="{W}" height="{HEIGHT}" '
        f'font-family="{font}" role="img" aria-labelledby="t d">',
        '<title id="t">The bicapped hexagonal antiprism</title>',
        '<desc id="d">Fourteen points on the unit sphere, rotating about the axis through the two poles: '
        'a regular hexagon at height h, a regular hexagon at height -h that is rotated by 30 degrees, '
        f'and the two poles. Its Coulomb energy {ENERGY} is the minimum for 14 points.</desc>',
        "<defs>",
        gradient("b", BLUE), gradient("g", GREEN), gradient("n", NEUTRAL),
        gradient("bf", BLUE, 0.52), gradient("gf", GREEN, 0.52), gradient("nf", NEUTRAL, 0.52),
        f'<radialGradient id="glass"><stop offset="0" stop-color="{TINT}" stop-opacity=".02"/>'
        f'<stop offset=".7" stop-color="{TINT}" stop-opacity=".05"/>'
        f'<stop offset=".92" stop-color="{RIM}" stop-opacity=".13"/>'
        f'<stop offset="1" stop-color="{RIM}" stop-opacity=".34"/></radialGradient>',
        '<radialGradient id="shine"><stop offset="0" stop-color="#fff" stop-opacity=".75"/>'
        '<stop offset=".5" stop-color="#fff" stop-opacity=".22"/>'
        '<stop offset="1" stop-color="#fff" stop-opacity="0"/></radialGradient>',
        '<radialGradient id="shadow"><stop offset="0" stop-color="#141a2a" stop-opacity=".19"/>'
        '<stop offset=".6" stop-color="#141a2a" stop-opacity=".06"/>'
        '<stop offset="1" stop-color="#141a2a" stop-opacity="0"/></radialGradient>',
        "</defs>",
        f'<rect x=".5" y=".5" width="{W - 1}" height="{HEIGHT - 1}" rx="14" fill="{PAGE}" stroke="{INK}" '
        'stroke-opacity=".1"/>',
        f'<ellipse cx="{CX}" cy="{CY + RAD + 25}" rx="{round(RAD * 0.8)}" ry="14" fill="url(#shadow)"/>',
        f'<circle cx="{CX}" cy="{CY}" r="{RAD}" fill="url(#glass)" stroke="{RIM}" stroke-opacity=".28"/>',
        "<g>", *points(0), "</g>",
        f'<g fill="{FACE}">', *faces(), "</g>",
        f'<g fill="none" stroke="{EDGE}" stroke-width="1.4" stroke-linecap="round">',
        f"<style>.u{{stroke:{BLUE};stroke-width:2.1}}.l{{stroke:{GREEN};stroke-width:2.1}}</style>",
        *edges(), "</g>",
        "<g>", *points(1), "</g>",
        f'<ellipse cx="{CX - 64}" cy="{CY - 86}" rx="54" ry="29" transform="rotate(-38 {CX - 64} {CY - 86})" '
        'fill="url(#shine)"/>',
        # the text, in the manner of the page lukasliehr.github.io/energy-minimization
        f'<text x="{TX}" y="92" font-size="13" fill="{MUTED}">Thomson problem for 14 points</text>',
        f'<text font-size="23" font-weight="600" fill="{INK}" letter-spacing="-.35">'
        f'<tspan x="{TX}" y="124">Bicapped hexagonal</tspan><tspan x="{TX}" y="152">antiprism</tspan></text>',
        f'<g font-size="14" fill="{INK2}">',
        legend(196, BLUE, f"Hexagon at height {h} ≈ 0.4554"),
        legend(224, GREEN, f"Hexagon at height −{h}, rotated by 30°"),
        legend(252, NEUTRAL, "Two poles"),
        "</g>",
        f'<line x1="{TX}" y1="280" x2="{W - 44}" y2="280" stroke="{INK}" stroke-opacity=".1"/>',
        f'<text x="{TX}" y="310" font-size="12" fill="{MUTED}">Coulomb energy</text>',
        f'<text x="{TX}" y="344" fill="{INK2}"><tspan font-size="27" font-weight="600" fill="{INK}" '
        f'letter-spacing="-.5">{ENERGY}</tspan><tspan dx="12" font-size="11" fill="{GOOD}">✓</tspan>'
        '<tspan dx="5" font-size="13">minimum</tspan></text>',
        "</svg>",
    ]
    return "\n".join(parts) + "\n"


if __name__ == "__main__":
    path = os.path.join(os.path.dirname(os.path.abspath(__file__)), "bicapped-hexagonal-antiprism.svg")
    check_loop()
    text = svg()
    with open(path, "w", encoding="utf-8") as f:
        f.write(text)
    print(path, len(text.encode()), "bytes")
