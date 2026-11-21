#!/usr/bin/env python3
"""Convert certificate JSON files into Lean data modules.

Certificates store data only (no bounds); every JSON number denotes exactly the decimal written,
and is emitted verbatim as a Lean literal of type ℚ (a non-decimal parameter is a "p/q" string).

Usage:  python3 scripts/json_to_lean.py [chapter ...]      (default: all known chapters)

Certificates are read from ../book_radii_polynomials/code/certificates/ (relative to the Lean
project `lean/`) and data modules are written to LeanearizedODEs/Data/ChNN.lean. The generated files must not be edited by hand.
"""
import json
import os
import sys
from fractions import Fraction

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
CERTS = os.path.join(ROOT, '..', 'book_radii_polynomials', 'code', 'certificates')
OUT = os.environ.get('JSON_TO_LEAN_OUT', os.path.join(ROOT, 'LeanearizedODEs', 'Data'))


def load(name):
    """Read a certificate, keeping the exact decimal text of every number."""
    with open(os.path.join(CERTS, name)) as fh:
        return json.load(fh, parse_float=str, parse_int=str)


def q(s):
    """A number (decimal text, or a "p/q" string) as a Lean term of type ℚ."""
    if '/' in s:
        f = Fraction(s)
        return f'({f.numerator} / {f.denominator} : ℚ)'
    Fraction(s)                       # validate
    return f'({s} : ℚ)'


def vec(v):
    return '![' + ', '.join(q(x) for x in v) + ']'


def mat(m):
    return '!![' + ';\n    '.join(', '.join(q(x) for x in row) for row in m) + ']'


def defn(name, ty, body, doc):
    return f'/-- {doc} -/\ndef {name} : {ty} :=\n  {body}\n'


def ch2():
    par = load('ch2_parabolas.json')
    lor = load('ch2_lorenz_equilibrium.json')
    out = []
    for k, sol in enumerate(par['solutions'], start=1):
        out.append(f'/-! ### Parabolas, approximate zero {k} -/\n')
        out.append(defn(f'parabolas_xbar_{k}', 'Fin 2 → ℚ', vec(sol['xbar']), 'approximate zero'))
        out.append(defn(f'parabolas_r0_{k}', 'ℚ', q(sol['r0']), 'radius `r₀` (existence)'))
        out.append(defn(f'parabolas_r1_{k}', 'ℚ', q(sol['r1']), 'radius `r₁` (uniqueness)'))
    out.append('/-! ### Lorenz equilibrium -/\n')
    out.append(defn('lorenz_xbar', 'Fin 3 → ℚ', vec(lor['xbar']), 'approximate zero'))
    out.append(defn('lorenz_A', 'Matrix (Fin 3) (Fin 3) ℚ', mat(lor['A']), 'approximate inverse'))
    out.append(defn('lorenz_r0', 'ℚ', q(lor['r0']), 'radius `r₀` (existence)'))
    out.append(defn('lorenz_r1', 'ℚ', q(lor['r1']), 'radius `r₁` (uniqueness)'))
    return ('Ch02', ['ch2_parabolas.json', 'ch2_lorenz_equilibrium.json'], out)


def arr(v):
    return '#[' + ', '.join(q(x) for x in v) + ']'


def lst(v):
    return '[' + ', '.join(q(x) for x in v) + ']'


def cq(z):
    """A complex number `[re, im]` as a Lean term of type ℚ × ℚ."""
    return f'({q(z[0])}, {q(z[1])})'


def clst(v):
    return '[' + ', '.join(cq(z) for z in v) + ']'


def carr(v):
    return '#[' + ', '.join(cq(z) for z in v) + ']'


def seq_block(prefix, cert, doc):
    """Data of a Chebyshev or Taylor certificate: N, nu, abar, the rows of A (if stored), r0, r1."""
    out = [f'/-! ### {doc} -/\n']
    out.append(defn(f'{prefix}_N', 'ℕ', str(cert['N']), 'truncation `N`'))
    out.append(defn(f'{prefix}_nu', 'ℚ', q(cert['nu']), 'weight `ν`'))
    for i, a in enumerate(cert['abar']):
        out.append(defn(f'{prefix}_abar_{i}', 'List ℚ', lst(a), f'approximate solution, component {i}'))
    n = len(cert['abar'])
    out.append(defn(f'{prefix}_abar', f'Fin {n} → List ℚ',
                    '![' + ', '.join(f'{prefix}_abar_{i}' for i in range(n)) + ']', 'approximate solution'))
    if 'A' in cert:
        for r, row in enumerate(cert['A']):
            out.append(defn(f'{prefix}_A_{r}', 'Array ℚ', arr(row), f'row {r} of `A^(N)`'))
        out.append(defn(f'{prefix}_A', 'Array (Array ℚ)',
                        '#[' + ', '.join(f'{prefix}_A_{r}' for r in range(len(cert['A']))) + ']',
                        'the rows of `A^(N)`, index `(j, k) ↦ j (N + 1) + k`'))
    out.append(defn(f'{prefix}_r0', 'ℚ', q(cert['r0']), 'radius `r₀` (existence)'))
    out.append(defn(f'{prefix}_r1', 'ℚ', q(cert['r1']), 'radius `r₁` (uniqueness)'))
    return out


def ch8():
    sc = load('ch8_scalar.json')
    out = ['/-! ### Scalar IVP (`N`, `ν` shared by the three initial values) -/\n']
    out.append(defn('scalar_N', 'ℕ', str(sc['N']), 'truncation `N`'))
    out.append(defn('scalar_nu', 'ℚ', q(sc['nu']), 'weight `ν`'))
    cases = [('half', 'x₀ = 1/2', sc), ('quarter', 'x₀ = 1/4', sc['figure_curves']['1/4']),
             ('threeQuarters', 'x₀ = 3/4', sc['figure_curves']['3/4'])]
    for name, x0, c in cases:
        out.append(f'/-! #### {x0} -/\n')
        out.append(defn(f'scalar_abar_{name}', 'List ℚ', lst(c['abar']), f'approximate solution, {x0}'))
        out.append(defn(f'scalar_r0_{name}', 'ℚ', q(c['r0']), f'radius `r₀` (existence), {x0}'))
        out.append(defn(f'scalar_r1_{name}', 'ℚ', q(c['r1']), f'radius `r₁` (uniqueness), {x0}'))
    out += seq_block('lorenz', load('ch8_lorenz.json'), 'Lorenz IVP')
    return ('Ch08', ['ch8_scalar.json', 'ch8_lorenz.json'], out)


def sh_block(prefix, cert, doc):
    """Data of a Swift-Hohenberg certificate: m, abar, the rows of A_m, and (nu, r0, r1) per proof."""
    out = [f'/-! ### {doc} -/\n']
    out.append(defn(f'{prefix}_m', 'ℕ', str(cert['m']), 'Galerkin dimension `m`'))
    out.append(defn(f'{prefix}_abar', 'List ℚ', lst(cert['abar']), 'approximate solution `ā_0, …, ā_{m-1}`'))
    for r, row in enumerate(cert['A_m']):
        out.append(defn(f'{prefix}_A_{r}', 'Array ℚ', arr(row), f'row {r} of `A_m`'))
    out.append(defn(f'{prefix}_A', 'Array (Array ℚ)',
                    '#[' + ', '.join(f'{prefix}_A_{r}' for r in range(len(cert['A_m']))) + ']',
                    'the rows of `A_m`'))
    for i, pr in enumerate(cert['proofs'], start=1):
        out.append(f'/-! #### Proof {i}: `ν = {pr["nu"]}` -/\n')
        out.append(defn(f'{prefix}_nu_{i}', 'ℚ', q(pr['nu']), 'weight `ν`'))
        out.append(defn(f'{prefix}_r0_{i}', 'ℚ', q(pr['r0']), 'radius `r₀` (existence)'))
        out.append(defn(f'{prefix}_r1_{i}', 'ℚ', q(pr['r1']), 'radius `r₁` (uniqueness)'))
    return out


def ch10():
    hopf = load('ch10_hopf.json')
    out = ['/-! ### Hopf bifurcation point of the Lorenz system -/\n']
    out.append(defn('hopf_Xbar', 'Fin 11 → ℚ', vec(hopf['Xbar']),
                    'approximate zero `X̄ = (x̄, v̄₁, v̄₂, ρ̄, ω̄)` of the Hopf map'))
    out.append(defn('hopf_xi1', 'Fin 3 → ℚ', vec(hopf['xi1']), 'phase vector `ξ₁` (`= v̄₁`)'))
    out.append(defn('hopf_xi2', 'Fin 3 → ℚ', vec(hopf['xi2']), 'phase vector `ξ₂` (`= v̄₂`)'))
    out.append(defn('hopf_A', 'Matrix (Fin 11) (Fin 11) ℚ', mat(hopf['A']), 'approximate inverse'))
    out.append(defn('hopf_r0', 'ℚ', q(hopf['r0']), 'radius `r₀` (existence)'))
    out.append(defn('hopf_r1', 'ℚ', q(hopf['r1']), 'radius `r₁` (uniqueness)'))
    helm = load('ch10_helmholtz.json')
    out.append('/-! ### The Helmholtz-Duffing equation -/\n')
    out.append(defn('helm_N', 'ℕ', str(helm['N']), 'truncation `N`'))
    out.append(defn('helm_nu', 'ℚ', q(helm['nu']), 'weight `ν`'))
    out.append(defn('helm_abar', 'List (ℚ × ℚ)', clst(helm['abar']),
                    'approximate solution `ā_{-N}, …, ā_N` (real and imaginary parts)'))
    N = int(helm['N'])
    for r in range(2 * N + 1):
        row = list(zip(helm['A_re'][r], helm['A_im'][r]))
        out.append(defn(f'helm_A_{r}', 'Array (ℚ × ℚ)', carr(row), f'row `{r - N}` of `A_N`'))
    out.append(defn('helm_A', 'Array (Array (ℚ × ℚ))',
                    '#[' + ', '.join(f'helm_A_{r}' for r in range(2 * N + 1)) + ']',
                    'the rows of `A_N`, row/column `n` at position `n + N`'))
    out.append(defn('helm_r0', 'ℚ', q(helm['r0']), 'radius `r₀` (existence)'))
    out.append(defn('helm_r1', 'ℚ', q(helm['r1']), 'radius `r₁` (uniqueness)'))
    lr = load('ch10_lorenz_LR.json')
    out.append('/-! ### The periodic orbit LR of the Lorenz system -/\n')
    out.append(defn('lr_N', 'ℕ', str(lr['N']), 'truncation `N`'))
    out.append(defn('lr_nu', 'ℚ', q(lr['nu']), 'weight `ν`'))
    out.append(defn('lr_xi', 'Fin 3 → ℚ', vec(lr['xi']), 'anchor point `ξ` of the phase condition'))
    out.append(defn('lr_tau', 'ℚ', q(lr['tau0bar']), 'approximate frequency `τ̄₀` (period `2π τ̄₀`)'))
    for j, a in enumerate(lr['abar']):
        out.append(defn(f'lr_abar_{j}', 'List (ℚ × ℚ)', clst(a),
                        f'approximate solution, component {j + 1}: `ā_{{{j + 1},k}}`, `k = -N, …, N`'))
    out.append(defn('lr_abar', 'Fin 3 → List (ℚ × ℚ)', '![lr_abar_0, lr_abar_1, lr_abar_2]',
                    'approximate solution'))
    for r in range(len(lr['A_re'])):
        row = list(zip(lr['A_re'][r], lr['A_im'][r]))
        out.append(defn(f'lr_A_{r}', 'Array (ℚ × ℚ)', carr(row), f'row {r} of `A^(N)`'))
    out.append(defn('lr_A', 'Array (Array (ℚ × ℚ))',
                    '#[' + ', '.join(f'lr_A_{r}' for r in range(len(lr['A_re']))) + ']',
                    'the rows of `A^(N)`, unknowns ordered `τ₀`, then `a_{j,k}` (`j = 1, 2, 3`, `k = -N, …, N`)'))
    out.append(defn('lr_r0', 'ℚ', q(lr['r0']), 'radius `r₀` (existence)'))
    out.append(defn('lr_r1', 'ℚ', q(lr['r1']), 'radius `r₁` (uniqueness)'))
    return ('Ch10', ['ch10_hopf.json', 'ch10_helmholtz.json', 'ch10_lorenz_LR.json'], out)


def ch13():
    out = sh_block('sh1', load('ch13_sh_lambda1.json'), 'Swift-Hohenberg, λ = 1') + \
        sh_block('sh10', load('ch13_sh_lambda10.json'), 'Swift-Hohenberg, λ = 10')
    return ('Ch13', ['ch13_sh_lambda1.json', 'ch13_sh_lambda10.json'], out)


def ch14():
    out = seq_block('scalar', load('ch14_scalar.json'), 'Scalar IVP') + \
        seq_block('lorenz', load('ch14_lorenz.json'), 'Lorenz IVP')
    return ('Ch14', ['ch14_scalar.json', 'ch14_lorenz.json'], out)


def ch15():
    out = seq_block('chafee', load('ch15_chafee_infante.json'), 'Chafee-Infante BVP')
    return ('Ch15', ['ch15_chafee_infante.json'], out)


CHAPTERS = {'2': ch2, '8': ch8, '10': ch10, '13': ch13, '14': ch14, '15': ch15}


def write(name, sources, defs):
    path = os.path.join(OUT, name + '.lean')
    with open(path, 'w') as fh:
        fh.write('module\n\npublic import Mathlib.LinearAlgebra.Matrix.Notation\n'
                 'public import Mathlib.Algebra.Order.Field.Rat\n\n')
        fh.write(f'/-!\n# Certificate data for the examples of Chapter {int(name[2:])}\n\n'
                 'Generated by `scripts/json_to_lean.py` from '
                 + ', '.join(f'`{s}`' for s in sources)
                 + '\n(in `LeanearizedODEs/book_radii_polynomials/code/certificates/`). Do not edit by hand.\n-/\n\n')
        fh.write('@[expose] public section\n\n')
        fh.write(f'namespace LeanearizedODEs.{name}Data\n\n')
        fh.write('\n'.join(defs))
        fh.write(f'\nend LeanearizedODEs.{name}Data\n')
    print('wrote', os.path.relpath(path, ROOT))


if __name__ == '__main__':
    for ch in sys.argv[1:] or sorted(CHAPTERS):
        write(*CHAPTERS[ch]())
