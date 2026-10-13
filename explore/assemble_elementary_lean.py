"""Copy only needed declarations into the independent elementary proof file.
Never modifies the original or zero-warning Lean versions.
"""
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parent.parent
src = (ROOT / 'IMO组合预选题_零告警.lean').read_text(encoding='utf-8-sig')


def declaration(name):
    match = re.search(r'(?m)^(?:noncomputable )?(?:def|theorem) ' + re.escape(name) + r'\b', src)
    assert match, name
    rest = src[match.start():]
    end = re.search(r'(?m)^(?:/--|/-!|(?:noncomputable )?(?:def|theorem) |namespace |end |#)', rest[1:])
    return (rest[:end.start()+1] if end else rest).rstrip() + '\n\n'


def module(name):
    text = (ROOT / name).read_text(encoding='utf-8-sig')
    return re.sub(r'^import Mathlib\s*', '', text, count=1).rstrip() + '\n\n'


header = '''import Mathlib

/-! # 极小整数 AP 覆盖的初等证明（2026-10-13）
独立新文件；原版和零告警版保持不变。
只复制 AP/lcm/素因子基础、CRT 位坐标桥与末步计数；
匹配存在性以有限最大化、单步改派、带证书的交替搜索和赋值反证证明。
不调用 Hall、严格亏格稳定性、Simpson 定理或旧主定理。
Searchable 记录可达槽的重排证书；最大 Searchable 集的封闭性替代显式路径列表。
它展开了增广的具体机制，没有引用增广路径存在性定理。
-/

namespace ElementaryAPProof

'''
names = ['MemAP', 'lcmDiff', 'bound', 'Essential', 'dvd_lcmDiff', 'lcmDiff_pos',
         'prime_pow_dvd_lcm_iff', 'exists_of_prime_pow_dvd_lcm_finset',
         'exists_of_prime_pow_dvd_lcmDiff', 'diffCount', 'sigma', 'diffCount_sum']
parts = [header] + [declaration(name) for name in names]
semantic = module('IMO组合预选题_初等路线研究.lean')
semantic = semantic[semantic.index('namespace ElementaryMatching'):]
parts += [module('explore/ElementaryAlternating.lean'), semantic,
          (ROOT / 'explore/ElementaryBoxTail.lean.txt').read_text(encoding='utf-8'),
          module('explore/MatchingCapacity.lean'),
          declaration('finite_box_capacity_bound').replace('MinimalCoverMatching.', 'ElementaryMatching.'),
          module('explore/DigitCoordinates.lean')]
start = src.index('namespace APDigitMatching')
end = src.index('end APDigitMatching', start) + len('end APDigitMatching')
parts += [src[start:end] + '\n\n']
for name in ['truncated_cover_bound', 'truncated_sum_add_sigma', 'T23prime',
             'card_ge_bound_of_allEssential', 'problem7']:
    parts += [declaration(name).replace('MinimalCoverMatching.', 'ElementaryMatching.')]
parts += ['''#print axioms truncated_cover_bound
#print axioms T23prime
#print axioms problem7

end ElementaryAPProof
''']
text = '\n'.join(parts).replace('MinimalCoverMatching.', 'ElementaryMatching.')
for forbidden in ['all_card_le_biUnion_card', 'HallMarriageTheorem.',
                  'strict_deficiency', 'sorry', 'Lean.ofReduceBool']:
    # Comments are removed before checking the proof source.
    proof_source = re.sub(r'/\-.*?\-/', '', text, flags=re.S)
    proof_source = re.sub(r'--[^\n]*', '', proof_source)
    assert forbidden not in proof_source, forbidden
audit = (ROOT / 'explore/ElementaryDependencyAudit.lean.txt').read_text(encoding='utf-8')
text = text.replace('end ElementaryAPProof\n', audit + '\nend ElementaryAPProof\n')
out = ROOT / 'IMO组合预选题_初等证明.lean'
out.write_text(text, encoding='utf-8')
print(out.name, len(text.splitlines()), 'lines')
