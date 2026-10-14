#!/usr/bin/env python3
"""Regenerate the import list of Elpi.lean from the modules under Elpi/ (except the CLI)."""
import glob
mods = sorted(m[:-5].replace('/', '.') for m in glob.glob('Elpi/**/*.lean', recursive=True) if 'Cli' not in m)
s = open('Elpi.lean').read()
head = s[s.index('/-!'):]
open('Elpi.lean', 'w').write('\n'.join('import ' + m for m in mods) + '\n\n' + head)
