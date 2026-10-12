theory Audit_GKPRST
  imports Majority_3CNF Majority_3CNF_Upper Majority_3CNF_Any
begin

text \<open>
  Trust audit for the formalization of Gurumukhani et al., as in \<open>Audit\<close>: the build fails
  unless the headline theorems depend on no oracle (\<open>skip_proof\<close> from \<open>sorry\<close> or
  \<open>quick_and_dirty\<close>, or any other).
\<close>

ML \<open>
  val headline =
    [@{thm gkprst_bound}, @{thm gkprst_half}, @{thm gkprst_half_odd}, @{thm IH_all},
     @{thm majority_mcnfs_slice}, @{thm majority_mcnfs}, @{thm majority_mcnfs_odd},
     @{thm majority_mcnfs_any}, @{thm majority_mcnfs_exp}, @{thm majority_mcnfs_exp_any},
     @{thm majority_mcnf_formula(1)}, @{thm majority_mcnf_formula(2)},
     @{thm good_perm}, @{thm greedy_cover}, @{thm threshold_cover},
     @{thm K4_thr}, @{thm K4_trans}, @{thm Q4_card},
     @{thm majority_mcnfs_upper}, @{thm majority_mcnfs_tight(1)}, @{thm majority_mcnfs_tight(2)},
     @{thm union_trans_card}, @{thm KC_trans_card}, @{thm XF(3)}, @{thm quarter_bound},
     @{thm majority_mcnfs_upper_any}, @{thm majority_mcnfs_tight_any(1)},
     @{thm majority_mcnfs_tight_any(2)}];
  val oracles = Thm_Deps.all_oracles headline;
  val _ =
    if null oracles then writeln "AUDIT OK: headline theorems depend on no oracles"
    else error ("AUDIT FAILED: oracles " ^ @{make_string} oracles);
\<close>

end
