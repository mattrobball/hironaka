#!/usr/bin/env python3
"""Draw the embedded resolution of the cusp y^2 = x^3 by three point blow-ups:
../static/cusp-sequence.svg.

Each panel is the real picture in the affine chart where the action is, with the chart coordinates
and the total transform of f = y^2 - x^3 (checked with sympy; see Blueprint/SchemeBlowUp.lean):

  stage 0, (x, y):  f = y^2 - x^3
  stage 1, (x, v), y = xv:  f = x^2 (v^2 - x)        E1 = {x = 0},  C1 = {x = v^2}, tangent to E1
  stage 2, (v, w), x = vw:  f = v^3 w^2 (v - w)      E2 = {v = 0},  E1 = {w = 0},  C2 = {v = w}
  stage 3, (v, s), w = vs:  f = v^6 s^2 (1 - s)      E3 = {v = 0},  E1 = {s = 0},  C3 = {s = 1};
                            E2 lies in the other chart, at s = infinity.
"""

import math
from pathlib import Path

OUT = Path(__file__).resolve().parent.parent / "static" / "cusp-sequence.svg"

PW, PH, GAP, TOP = 200, 200, 46, 58  # panel size, gap, top margin
W = 4 * PW + 3 * GAP + 40
H = TOP + PH + 118

C_COL, E1, E2, E3 = "#1e8449", "#c0392b", "#2e6fbd", "#8e44ad"
FONT = 'font-family="STIX Two Text, Cambria Math, DejaVu Serif, Georgia, serif"'


def panel_origin(k):
    return 20 + k * (PW + GAP), TOP


def path(points, colour, width=2.6, dash=None):
    d = "M " + " L ".join(f"{x:.1f},{y:.1f}" for x, y in points)
    extra = f' stroke-dasharray="{dash}"' if dash else ""
    return (f'<path d="{d}" fill="none" stroke="{colour}" stroke-width="{width}" '
            f'stroke-linecap="round"{extra}/>')


def text(x, y, s, size=14, anchor="middle", fill="#222", italic=False):
    st = ' font-style="italic"' if italic else ""
    return (f'<text x="{x:.1f}" y="{y:.1f}" font-size="{size}" text-anchor="{anchor}" '
            f'fill="{fill}" {FONT}{st}>{s}</text>')


def dot(x, y, colour="#222", r=4):
    return f'<circle cx="{x:.1f}" cy="{y:.1f}" r="{r}" fill="{colour}"/>'


def to_px(k, u, v, span=1.25):
    """Chart coordinates (u, v) in [-span, span]^2 to pixels in panel k."""
    ox, oy = panel_origin(k)
    return ox + PW / 2 + u / span * PW / 2 * 0.9, oy + PH / 2 - v / span * PH / 2 * 0.9


def axes(k, xl, yl):
    out = []
    a, b = to_px(k, -1.2, 0), to_px(k, 1.2, 0)
    c, d = to_px(k, 0, -1.2), to_px(k, 0, 1.2)
    out.append(path([a, b], "#bbb", 1))
    out.append(path([c, d], "#bbb", 1))
    out.append(text(b[0] + 2, b[1] + 16, xl, 12, "end", "#777", True))
    out.append(text(d[0] + 10, d[1] + 4, yl, 12, "start", "#777", True))
    return out


def main():
    svg = [f'<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 {W} {H}" width="{W}" height="{H}">',
           f'<rect width="{W}" height="{H}" fill="#fffdf8"/>']
    for k in range(4):
        ox, oy = panel_origin(k)
        svg.append(f'<rect x="{ox}" y="{oy}" width="{PW}" height="{PH}" fill="#f7f5ee" '
                   f'stroke="#d6d1c4" rx="6"/>')

    heads = ["stage 0: the cusp", "blow up the origin", "blow up the tangency", "blow up the triple point"]
    for k, h in enumerate(heads):
        ox, _ = panel_origin(k)
        svg.append(text(ox + PW / 2, TOP - 30, h, 14))
    for k, h in enumerate(["coordinates (x, y)", "chart y = xv", "chart x = vw", "chart w = vs"]):
        ox, _ = panel_origin(k)
        svg.append(text(ox + PW / 2, TOP - 12, h, 12, fill="#666", italic=True))

    # Arrows between panels: pi_i goes right-to-left.
    for k in range(3):
        ox, oy = panel_origin(k)
        x0, x1, y = ox + PW + GAP - 8, ox + PW + 8, oy + PH / 2
        svg.append(path([(x0, y), (x1, y)], "#555", 1.6))
        svg.append(path([(x1 + 7, y - 5), (x1, y), (x1 + 7, y + 5)], "#555", 1.6))
        svg.append(text((x0 + x1) / 2, y - 8, f"π{'₀₁₂'[k]}", 13, fill="#555", italic=True))

    # Stage 0: y^2 = x^3.
    svg += axes(0, "x", "y")
    ts = [i / 60 for i in range(61)]
    up = [to_px(0, t * 1.1, (t * 1.1) ** 1.5) for t in ts]
    down = [to_px(0, t * 1.1, -((t * 1.1) ** 1.5)) for t in ts]
    svg.append(path(list(reversed(up)) + down, C_COL))
    svg.append(dot(*to_px(0, 0, 0)))
    svg.append(text(*to_px(0, 0.55, 1.05), "C", 15, fill=C_COL, italic=True))

    # Stage 1: E1 = {x = 0}, C1 = {x = v^2}.
    svg += axes(1, "x", "v")
    svg.append(path([to_px(1, 0, -1.2), to_px(1, 0, 1.2)], E1))
    par = [to_px(1, v * v, v) for v in [-1.05 + 2.1 * i / 60 for i in range(61)]]
    svg.append(path(par, C_COL))
    svg.append(dot(*to_px(1, 0, 0)))
    svg.append(text(*to_px(1, -0.3, 1.02), "E₁", 14, fill=E1))
    svg.append(text(*to_px(1, 0.95, 0.75), "C₁", 14, fill=C_COL, italic=True))

    # Stage 2: E2 = {v = 0} (vertical), E1 = {w = 0} (horizontal), C2 = {v = w}.
    svg += axes(2, "v", "w")
    svg.append(path([to_px(2, 0, -1.2), to_px(2, 0, 1.2)], E2))
    svg.append(path([to_px(2, -1.2, 0), to_px(2, 1.2, 0)], E1))
    svg.append(path([to_px(2, -1.0, -1.0), to_px(2, 1.0, 1.0)], C_COL))
    svg.append(dot(*to_px(2, 0, 0)))
    svg.append(text(*to_px(2, -0.3, 1.02), "E₂", 14, fill=E2))
    svg.append(text(*to_px(2, -1.0, 0.14), "E₁", 14, fill=E1))
    svg.append(text(*to_px(2, 0.95, 0.72), "C₂", 14, fill=C_COL, italic=True))

    # Stage 3: E3 = {v = 0}, drawn horizontally along s; E1 at s = 0, C3 at s = 1, E2 at s = inf.
    ox, oy = panel_origin(3)
    yE = oy + PH / 2
    svg.append(path([(ox + 14, yE), (ox + PW - 14, yE)], E3))
    for sx, col, lab, it in [(0.22, E1, "E₁", False), (0.5, C_COL, "C₃", True), (0.78, E2, "E₂", False)]:
        x = ox + PW * sx
        svg.append(path([(x, yE - 62), (x, yE + 62)], col))
        svg.append(dot(x, yE, "#222", 3))
        svg.append(text(x, yE - 70, lab, 14, fill=col, italic=it))
    svg.append(text(ox + PW - 16, yE - 8, "E₃", 14, "end", E3))
    svg.append(text(ox + PW * 0.22, yE + 80, "s = 0", 11, fill="#777", italic=True))
    svg.append(text(ox + PW * 0.5, yE + 80, "s = 1", 11, fill="#777", italic=True))
    svg.append(text(ox + PW * 0.78, yE + 80, "s = ∞", 11, fill="#777", italic=True))

    # Captions: the total transform of f at each stage, and what is wrong.
    caps = [
        ("f = y² − x³", "singular point", "#b03a2e"),
        ("f = x²(v² − x)", "C₁ smooth, tangent to E₁", "#b9770e"),
        ("f = v³w²(v − w)", "three curves through a point", "#b9770e"),
        ("f = v⁶s²(1 − s)", "simple normal crossings", "#1e8449"),
    ]
    for k, (a, b, col) in enumerate(caps):
        ox, oy = panel_origin(k)
        svg.append(text(ox + PW / 2, oy + PH + 24, a, 14))
        svg.append(text(ox + PW / 2, oy + PH + 44, b, 13, fill=col))
    ox0, _ = panel_origin(0)
    svg.append(text(W / 2, H - 22,
                    "total transform of C in the last stage:  6E₃ + 3E₂ + 2E₁ + C₃"
                    "   (multiplicities read off the exponents)", 13, fill="#444"))
    svg.append("</svg>")
    OUT.parent.mkdir(exist_ok=True)
    OUT.write_text("\n".join(svg))
    print(OUT)


if __name__ == "__main__":
    main()
