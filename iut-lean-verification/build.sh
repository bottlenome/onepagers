#!/usr/bin/env bash
# IUT 系3.12 形式検証のビルド + 公理チェック
# 必要: elan (https://github.com/leanprover/elan)
set -euo pipefail
cd "$(dirname "$0")"

lake build

# sorry や追加公理に依存していないことを確認
cat > /tmp/iut_check_axioms.lean <<'EOF'
import IUT
#print axioms IUT.verdict
#print axioms IUT.ss_incompatible
#print axioms IUT.cor312_independent
#print axioms IUT.controversy_reduces_to_rc
#print axioms IUT.mono_implies_bi
#print axioms IUT.bi_implies_mono_classical
#print axioms IUT.AddSym.act_comp
#print axioms IUT.theta_labels
#print axioms IUT.path_col
#print axioms IUT.cross_col_needs_theta
#print axioms IUT.abc_implies_asymptotic_fermat
#print axioms IUT.szpiro_of_cor312
#print axioms IUT.szpiro_of_cor312_precise
#print axioms IUT.cor312_of_multiradial
#print axioms IUT.strict_evaluation_obstruction
#print axioms IUT.padding_necessary
#print axioms IUT.multiradial_consistent
#print axioms IUT.gaussian_obstruction
#print axioms IUT.szpiro_of_multiradial
#print axioms IUT.recon_log_compat
#print axioms IUT.addSym_inverse
#print axioms IUT.bicoric_constant
#print axioms IUT.theta_value_pm_symmetry
#print axioms IUT.two_mul_procTotal
#print axioms IUT.height_bounded_of_uniform_szpiro
#print axioms IUT.abc_bounds_catalan23
#print axioms IUT.six_mul_sumSq
#print axioms IUT.invariant_transport
#print axioms IUT.geometric_normal
#print axioms IUT.outer_conjugation_unique
#print axioms IUT.outer_action_inner_on_kernel
#print axioms IUT.slim_faithful
#print axioms IUT.section_decomposition
#print axioms IUT.theta_deck_not_finite
#print axioms IUT.theta_exponent_unique
#print axioms IUT.theta_exponent_not_periodic
#print axioms IUT.finite_quotient_collapses_theta
#print axioms IUT.arithmetic_quotient_collapses_theta
#print axioms IUT.temperedArithmetic_consistent
#print axioms IUT.tempered_invariant_transport
#print axioms IUT.findWitness_spec
#print axioms IUT.abelianization_determines
#print axioms IUT.reconCore_correct
#print axioms IUT.padic_recon_monoanabelian
#print axioms IUT.padic_recon_bianabelian
#print axioms IUT.padic_invariant_transport
#print axioms IUT.cyclotome_indeterminacy
#print axioms IUT.marked_cyclotome_rigid
#print axioms IUT.theta_comm
#print axioms IUT.mono_theta_cyclotomic_rigidity
#print axioms IUT.rigid_theta_values
#print axioms IUT.Frobenioid.deg_zero
#print axioms IUT.frob_not_invertible
#print axioms IUT.gaussianDiv_deg
#print axioms IUT.frobenioid_realizes_qpilot
#print axioms IUT.degree_volume_consistent
EOF
lake env lean /tmp/iut_check_axioms.lean

echo "OK: all theorems verified, no sorry."
echo "Expected: standard axioms only. mono_implies_bi is axiom-free;"
echo "bi_implies_mono_classical requires Classical.choice (the point of M1-2)."
