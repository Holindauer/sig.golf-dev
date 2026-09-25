"""Validate optional, untrusted display data from a frozen PR commit."""
from __future__ import annotations

import json
import re
import xml.etree.ElementTree as ET

MAX_PRESENTATION_BYTES = 64 * 1024
SVG_NS = 'http://www.w3.org/2000/svg'
SVG_TAGS = {'svg', 'g', 'path', 'rect', 'circle', 'ellipse', 'line', 'polyline', 'polygon',
            'text', 'tspan', 'title', 'desc', 'defs', 'linearGradient', 'radialGradient', 'stop'}
SVG_ATTRIBUTES = {'xmlns', 'viewBox', 'width', 'height', 'x', 'y', 'x1', 'x2', 'y1', 'y2',
                  'cx', 'cy', 'r', 'rx', 'ry', 'd', 'points', 'transform', 'fill', 'stroke',
                  'stroke-width', 'stroke-linecap', 'stroke-linejoin', 'opacity',
                  'fill-opacity', 'stroke-opacity', 'font-size', 'font-family',
                  'text-anchor', 'font-weight', 'id', 'offset', 'stop-color', 'stop-opacity',
                  'gradientUnits', 'gradientTransform', 'fx', 'fy'}
MNEMONIC = re.compile(r'[A-Z][A-Z0-9.]{1,11}\Z')
MULTIPLY_DIVIDE = {'MUL', 'MULH', 'MULHSU', 'MULHU', 'MULW', 'DIV', 'DIVU', 'DIVW', 'DIVUW',
                   'REM', 'REMU', 'REMW', 'REMUW'}
INTEGER = re.compile(r'0|[1-9][0-9]*\Z')


class PresentationError(ValueError):
    pass


def validate_json(raw: bytes, claim: dict) -> dict:
    if len(raw) > MAX_PRESENTATION_BYTES:
        raise PresentationError('presentation.json exceeds 64 KiB')
    try:
        value = json.loads(raw)
    except (UnicodeError, ValueError, RecursionError) as exc:
        raise PresentationError('presentation.json is not valid JSON') from exc
    if not isinstance(value, dict) or set(value) - {'version', 'summary', 'facts', 'profile', 'diagram'} or value.get('version') != 1:
        raise PresentationError('presentation.json has unknown fields or version')
    if 'diagram' in value and type(value['diagram']) is not bool:
        raise PresentationError('diagram must be a boolean')
    summary = value.get('summary')
    if not isinstance(summary, str) or not 1 <= len(summary) <= 500 or any(ord(c) < 32 and c not in '\n\t' for c in summary):
        raise PresentationError('summary must be 1–500 plain-text characters')
    facts = value.get('facts', [])
    if not isinstance(facts, list) or len(facts) > 8:
        raise PresentationError('facts must contain at most 8 rows')
    for fact in facts:
        if not isinstance(fact, dict) or set(fact) != {'label', 'value'}:
            raise PresentationError('each fact needs label and value')
        if not all(isinstance(fact[k], str) and 1 <= len(fact[k]) <= limit and '\n' not in fact[k]
                   for k, limit in [('label', 40), ('value', 120)]):
            raise PresentationError('fact text is too long or invalid')
    profile = value.get('profile')
    if profile is not None:
        if not isinstance(profile, dict) or set(profile) != {'samples', 'method', 'instructions', 'hashes'}:
            raise PresentationError('profile needs samples, method, instructions, and hashes')
        samples, method, counts, hashes = (profile[k] for k in ('samples', 'method', 'instructions', 'hashes'))
        if type(samples) is not int or not 1 <= samples <= 1_000_000:
            raise PresentationError('samples must be 1–1,000,000')
        if not isinstance(method, str) or not 1 <= len(method) <= 200 or '\n' in method:
            raise PresentationError('method must be a short plain-text sampling description')
        if (not isinstance(counts, dict) or not 1 <= len(counts) <= 80 or 'HALT' not in counts or
                not isinstance(hashes, dict) or len(counts) + len(hashes) > 80):
            raise PresentationError('profile needs HALT and at most 80 total rows')
        if any(not isinstance(key, str) or not MNEMONIC.fullmatch(key) or key in {'HASH', 'ECALL', 'EBREAK'} or
               type(count) is not int or count < 0 or count > claim['C'] * samples
               for key, count in counts.items()):
            raise PresentationError('ordinary instruction counts are invalid')
        if counts['HALT'] != samples:
            raise PresentationError('each accepting run must execute one HALT')
        if any(not isinstance(bits, str) or not INTEGER.fullmatch(bits) or len(bits) > 9 or int(bits) > 2**27 or
               int(bits) % 64 or type(count) is not int or count < 1 or count > claim['C'] * samples
               for bits, count in hashes.items()):
            raise PresentationError('HASH counts must be grouped by input bit length, a multiple of 64')
        blocks = sum(count * max(1, (int(bits) + 511) // 512) for bits, count in hashes.items())
        instructions = sum(count * (4 if key in MULTIPLY_DIVIDE else 1) for key, count in counts.items())
        cycles = instructions + 8 * blocks + samples * ((claim['W'] + 255) // 256)
        if cycles > claim['C'] * samples:
            raise PresentationError('reported average cycles exceed the certified bound')
    return value


def validate_svg(raw: bytes) -> None:
    if len(raw) > MAX_PRESENTATION_BYTES:
        raise PresentationError('scheme.svg exceeds 64 KiB')
    if re.search(br'<!\s*(?:DOCTYPE|ENTITY)|<\?(?!xml\s)', raw, re.I):
        raise PresentationError('SVG must not contain a DTD or entity declaration')
    try:
        root = ET.fromstring(raw)
    except ET.ParseError as exc:
        raise PresentationError('scheme.svg is not valid XML') from exc
    if root.tag != '{' + SVG_NS + '}svg' or 'viewBox' not in root.attrib:
        raise PresentationError('scheme.svg needs an SVG root and viewBox')
    try:
        view = [float(n) for n in root.attrib['viewBox'].replace(',', ' ').split()]
    except ValueError as exc:
        raise PresentationError('invalid SVG viewBox') from exc
    if len(view) != 4 or not all(abs(n) < 100000 for n in view) or view[2] <= 0 or view[3] <= 0:
        raise PresentationError('invalid SVG viewBox')
    for element in root.iter():
        if element.tag not in {'{' + SVG_NS + '}' + tag for tag in SVG_TAGS}:
            raise PresentationError('scheme.svg contains a forbidden element')
        for attribute, content in element.attrib.items():
            if attribute not in SVG_ATTRIBUTES or len(content) > 8192 or re.search(r'url\s*\(|javascript:|data:', content, re.I):
                raise PresentationError('scheme.svg contains a forbidden attribute or URL')
