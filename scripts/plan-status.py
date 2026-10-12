#!/usr/bin/env python3
"""Recompute the summary tables in PLAN.md from the detail files in plan/.

Each plan/NN-*.md file (or plan/X-*.md for parts outside the manuscript) starts
with '# N. Title (Source)' and lists its
sub-problems as '### Name' headings, each followed by a table of rows
'| Subcomponent | Files | Mathematics | Tape | Notes |'. This script rewrites
the PLAN.md overview row and the section's sub-problem table.

Each sub-problem names a math and a tape milestone, as lines
'- Math milestone: `Full.Lean.name` — statement' (or '- Math milestone: —' when
the column does not apply). A milestone is done when that theorem is declared in
a file the IntegerMultBounds root imports; the axiom audit already rejects any
sorry there. A sub-problem shows ✅ when its milestone is done, 🟡 with its
finished-row count when only some rows are done, and ⬜ otherwise. The overview
counts done milestones per section. Files counts the distinct Lean files named
in the Files column (names that match no file count as planned).

Usage: python3 scripts/plan-status.py [--check] [--list]
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

DECLARATION = re.compile(r'^\s*(?:@\[[^\]]*\]\s*)*(?:(?:private|protected|noncomputable|nonrec|partial|unsafe)\s+)*'
                         r'(?:theorem|lemma|def|abbrev|instance|structure|inductive|class)\s+([^\s(:{\[]+)')


def imported_modules():
    seen = set()
    pending = ['IntegerMultBounds']
    while pending:
        module = pending.pop()
        if module in seen:
            continue
        seen.add(module)
        path = os.path.join(ROOT, module.replace('.', '/') + '.lean')
        if not os.path.exists(path):
            continue
        for line in open(path):
            found = re.match(r'^import\s+(IntegerMultBounds\S*)', line)
            if found:
                pending.append(found.group(1))
    return seen


def declared_names():
    names = set()
    for module in imported_modules():
        path = os.path.join(ROOT, module.replace('.', '/') + '.lean')
        if not os.path.exists(path):
            continue
        scopes = []
        in_comment = 0
        for line in open(path):
            was_comment = in_comment > 0
            in_comment += line.count('/-') - line.count('-/')
            if was_comment or in_comment > 0 or line.lstrip().startswith('--'):
                continue
            opening = re.match(r'^\s*(namespace|section)\b\s*(\S*)', line)
            if opening:
                scopes.append(opening.group(2) if opening.group(1) == 'namespace' else '')
                continue
            if re.match(r'^\s*(noncomputable\s+section|mutual)\b', line):
                scopes.append('')
                continue
            if re.match(r'^\s*end\b', line):
                if scopes:
                    scopes.pop()
                continue
            declaration = DECLARATION.match(line)
            if declaration:
                name = declaration.group(1)
                if name.startswith('_root_.'):
                    names.add(name[len('_root_.'):])
                else:
                    names.add('.'.join([scope for scope in scopes if scope] + [name]))
    return names
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


def row_status(rows, column):
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


MILESTONE = re.compile(r'^- (Math|Tape) milestone: (?:`([^`]+)`|—)')


def milestone_status(group, column, declared):
    name = group['milestones'].get(column)
    if name is None:
        return '?' if group['rows'] else '—'
    if name == '':
        return '—'
    if name in declared:
        return '✅'
    rows = row_status(group['rows'], 2 if column == 'Math' else 3)
    if rows.startswith('✅') or rows.startswith('🟡'):
        done, total = rows.split()[1].split('/')
        return '🟡' if done == total else f'🟡 {done}/{total} rows'
    return '⬜'


def section_status(groups, column, declared):
    named = [group for group in groups if group['milestones'].get(column)]
    if not named:
        return '—'
    done = sum(group['milestones'][column] in declared for group in named)
    if done == len(named):
        return f'✅ {done}/{len(named)}'
    started = any(milestone_status(group, column, declared) != '⬜' for group in named)
    return f'{"🟡" if done or started else "⬜"} {done}/{len(named)}'


def file_count(rows):
    files = set()
    for row in rows:
        files |= resolve(cells(row)[1])
    return len(files)


def read_section(path):
    lines = open(path).read().split('\n')
    heading = re.match(r'^# (\d+|[A-Z])\. (.*)$', lines[0])
    groups = []
    for line in lines[1:]:
        if line.startswith('### '):
            groups.append({'name': line[4:].strip(), 'rows': [], 'milestones': {}})
        elif line.startswith('## '):
            groups.append({'name': None, 'rows': [], 'milestones': {}})
        elif groups and groups[-1]['name']:
            milestone = MILESTONE.match(line)
            if milestone:
                groups[-1]['milestones'][milestone.group(1)] = milestone.group(2) or ''
            elif line.startswith('| ') and not line.startswith('| ---') and not line.startswith('| Subcomponent'):
                groups[-1]['rows'].append(line)
    groups = [group for group in groups if group['name'] and (group['rows'] or group['milestones'])]
    return heading.group(1), heading.group(2), groups


def main():
    plan_path = os.path.join(ROOT, 'PLAN.md')
    text = open(plan_path).read()
    lines = text.split('\n')
    overview = {}
    tables = {}
    declared = declared_names()
    problems = []
    for path in sorted(glob.glob(os.path.join(ROOT, 'plan', '[0-9][0-9]-*.md')) +
                      glob.glob(os.path.join(ROOT, 'plan', '[A-Z]-*.md'))):
        number, heading, groups = read_section(path)
        relative = os.path.relpath(path, ROOT)
        title = re.sub(r' \((.*)\)$', '', heading)
        source = re.search(r'\((.*)\)$', heading)
        rows = [row for group in groups for row in group['rows']]
        overview[relative] = (f'| [{title}]({relative}) | {source.group(1) if source else "—"} | '
                              f'{section_status(groups, "Math", declared)} | '
                              f'{section_status(groups, "Tape", declared)} | {file_count(rows)} |')
        tables[number] = [f'| {group["name"]} | {milestone_status(group, "Math", declared)} | '
                          f'{milestone_status(group, "Tape", declared)} | {file_count(group["rows"])} |'
                          for group in groups]
        for group in groups:
            for column in ('Math', 'Tape'):
                name = group['milestones'].get(column)
                if name is None:
                    problems.append(f'{relative}: {group["name"]}: no {column} milestone line')
                if '--list' in sys.argv and name:
                    print(f'{"done" if name in declared else "open"}\t{column}\t{name}')
    output = []
    section = None
    index = 0
    while index < len(lines):
        line = lines[index]
        heading = re.match(r'^## (\d+|[A-Z])\. ', line)
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
    for problem in problems:
        print(problem)
    if '--check' in sys.argv:
        if new_text != text or problems:
            if new_text != text:
                print('PLAN.md summary tables are out of date; run python3 scripts/plan-status.py')
            sys.exit(1)
        return
    if new_text != text:
        open(plan_path, 'w').write(new_text)
        print('PLAN.md updated')


if __name__ == '__main__':
    main()
