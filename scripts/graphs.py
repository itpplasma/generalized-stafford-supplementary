"""Graphviz helpers shared by the overview and the Lean graph page."""
import re, subprocess

from common import esc


def wrap(text, width):
    lines = []
    for para in text.split('\n'):
        line = ''
        for word in para.split(' '):
            if line and len(line) + 1 + len(word) > width:
                lines.append(line)
                line = word
            else:
                line = f'{line} {word}' if line else word
        lines.append(line)
    return lines


def name_lines(name, width):
    """Break a Lean name after underscores and dots so it fits `width`."""
    lines, line = [], ''
    for part in [p for p in name.replace('_', '_\0').replace('.', '.\0').split('\0') if p]:
        if line and len(line) + len(part) > width:
            lines.append(line)
            line = part
        else:
            line += part
    return lines + [line]


def label(title, body, small=None, width=34, small_lines=None):
    parts = [f'<B>{esc(title)}</B>'] if title else []
    parts += [esc(line) for line in wrap(body, width)] if body else []
    if small:
        parts += [f'<FONT POINT-SIZE="7.5">{esc(line)}</FONT>' for line in (small_lines or wrap(small, width + 6))]
    return '<' + '<BR/>'.join(parts) + '>'


def node(key, lab, cls, **attrs):
    extra = ''.join(f' {k}="{v}"' for k, v in attrs.items())
    return f'  "{key}" [label={lab} class="{cls}"{extra}];\n'


HEAD = ('  graph [fontname="Arial" fontsize=10 nodesep=0.16 ranksep=0.3 pad=0.05 bgcolor="transparent"];\n'
        '  node [shape=box style="rounded" fontname="Arial" fontsize=9 margin="0.1,0.04" height=0.3];\n'
        '  edge [arrowsize=0.55 penwidth=0.9];\n')


def render(dot):
    return subprocess.run(['dot', '-Tsvg'], input=dot, capture_output=True, text=True, check=True).stdout


def width(dot):
    return float(re.search(r'<svg width="([\d.]+)pt"', render(dot))[1]) * 4 / 3


def svg(dot, shrink=True, title=None):
    """Inline SVG: scales down to the container when `shrink`, keeps links."""
    out = render(dot)
    out = out[out.index('<svg'):]
    cap = 'max-width:100%' if shrink else 'max-width:none'
    role = f'role="img" aria-label="{esc(title)}"' if title else 'role="img"'
    out = re.sub(r'<svg width="([\d.]+)pt" height="([\d.]+)pt"',
                 lambda m: f'<svg {role} style="width:{float(m[1]) * 4 / 3:.0f}px;{cap}"', out)
    out = re.sub(r'<title>[^<]*</title>\n?', '', out)
    out = re.sub(r'<!--.*?-->\n?', '', out, flags=re.S)
    return out.replace('xlink:href=', 'href=').replace('xlink:title=', 'data-title=')


FILL = dict(cited='cited', std='std', hyp='hyp', dep='dep', step='step', stmt='dep', goal='goal')
SVG_CSS = ('svg text{fill:var(--fg)!important;font-family:Arial,"Liberation Sans",Arimo,Helvetica,sans-serif}'
           'svg .edge path{stroke:var(--edge)}svg .edge polygon{fill:var(--edge);stroke:var(--edge)}'
           'svg .node path,svg .node polygon,svg .node ellipse{stroke-width:1.2}'
           'svg a:hover path,svg a:hover polygon,svg a:focus path,svg a:focus polygon{stroke-width:2.2}'
           + ''.join(f'svg .node.{c} path,svg .node.{c} polygon{{fill:var(--{v});stroke:var(--{v}k)}}'
                     for c, v in FILL.items())
           + 'svg .node.goal path,svg .node.goal polygon{stroke-width:1.6}')
