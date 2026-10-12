#!/usr/bin/env python3
"""Recompute the summary tables in PLAN.md from the detail files in plan/.

Each plan/NN-*.md file starts with '# N. Title (Source)' and lists its
sub-problems as '### Name' headings, each followed by a table of rows
'| Subcomponent | Files | Mathematics | Tape | Notes |'. This script rewrites
the PLAN.md overview row and the section's sub-problem table: Mathematics and
Tape count ✅ rows out of rows not marked —, and Files counts the distinct Lean
files named in the Files column (names that match no file count as planned).

Usage: python3 scripts/plan-status.py [--check]
"""
import collections
import glob
import os
import re
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))


def lean_files():
    names = collections.defaultdict(set)
    for directory, _, files in os.walk(os.path.join(ROOT, 'IntegerMultBounds')):
        for file in files:
            if file.endswith('.lean'):
                path = os.path.relpath(os.path.join(directory, file), os.path.join(ROOT, 'IntegerMultBounds'))[:-5]
                names[path].add(path)
                names[path.split('/')[-1]].add(path)
    for file in glob.glob(os.path.join(ROOT, '*.lean')):
        name = os.path.basename(file)[:-5]
        names[name].add('../' + name)
    return names


NAMES = lean_files()
ALL_PATHS = set().union(*NAMES.values())


def resolve(cell):
    found = set()
    for name in re.findall(r'`([^`]+)`', cell):
        name = name.replace('.lean', '')
        if name.endswith('/*'):
            found |= {path for path in ALL_PATHS if ('/' + name[:-1]) in '/' + path}
        elif name in NAMES:
            found |= NAMES[name]
        elif name.split('.')[0] in NAMES:
            found |= NAMES[name.split('.')[0]]
        elif name.replace('.', '/') in NAMES:
            found |= NAMES[name.replace('.', '/')]
        else:
            found.add('planned:' + name)
    return found


def cells(row):
    return [cell.strip() for cell in row.strip().strip('|').split(' | ')]


def status(rows, column):
    values = [cells(row)[column] for row in rows]
    counted = [value for value in values if value != '—']
    if not counted:
        return '—'
    done = sum(value == '✅' for value in counted)
    if done == len(counted):
        symbol = '✅'
    elif any(value in ('✅', '🟡') for value in counted):
        symbol = '🟡'
    else:
        symbol = '⬜'
    return f'{symbol} {done}/{len(counted)}'


def file_count(rows):
    files = set()
    for row in rows:
        files |= resolve(cells(row)[1])
    return len(files)


def read_section(path):
    lines = open(path).read().split('\n')
    heading = re.match(r'^# (\d+)\. (.*)$', lines[0])
    groups = []
    for line in lines[1:]:
        if line.startswith('### '):
            groups.append((line[4:].strip(), []))
        elif line.startswith('## '):
            groups.append((None, []))
        elif groups and groups[-1][0] and line.startswith('| ') \
                and not line.startswith('| ---') and not line.startswith('| Subcomponent'):
            groups[-1][1].append(line)
    groups = [(name, rows) for name, rows in groups if name and rows]
    return heading.group(1), heading.group(2), groups


def main():
    plan_path = os.path.join(ROOT, 'PLAN.md')
    text = open(plan_path).read()
    lines = text.split('\n')
    overview = {}
    tables = {}
    for path in sorted(glob.glob(os.path.join(ROOT, 'plan', '[0-9][0-9]-*.md'))):
        number, heading, groups = read_section(path)
        relative = os.path.relpath(path, ROOT)
        title = re.sub(r' \((.*)\)$', '', heading)
        source = re.search(r'\((.*)\)$', heading)
        rows = [row for _, group_rows in groups for row in group_rows]
        overview[relative] = (f'| [{title}]({relative}) | {source.group(1) if source else "—"} | '
                              f'{status(rows, 2)} | {status(rows, 3)} | {file_count(rows)} |')
        tables[number] = [f'| {name} | {status(group_rows, 2)} | {status(group_rows, 3)} | {file_count(group_rows)} |'
                          for name, group_rows in groups]
    output = []
    section = None
    index = 0
    while index < len(lines):
        line = lines[index]
        heading = re.match(r'^## (\d+)\. ', line)
        if heading:
            section = heading.group(1)
        elif line.startswith('## '):
            section = None
        link = re.match(r'^\| \[[^\]]*\]\((plan/[^)]*)\) \|', line)
        if link and link.group(1) in overview:
            output.append(overview[link.group(1)])
            index += 1
            continue
        if line.startswith('| Sub-problem |') and section in tables:
            output += [line, lines[index + 1]] + tables[section]
            index += 2
            while index < len(lines) and lines[index].startswith('|'):
                index += 1
            continue
        output.append(line)
        index += 1
    new_text = '\n'.join(output)
    if '--check' in sys.argv:
        if new_text != text:
            print('PLAN.md summary tables are out of date; run python3 scripts/plan-status.py')
            sys.exit(1)
        return
    if new_text != text:
        open(plan_path, 'w').write(new_text)
        print('PLAN.md updated')


if __name__ == '__main__':
    main()
