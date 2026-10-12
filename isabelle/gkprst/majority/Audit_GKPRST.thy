theory Audit_GKPRST
  imports Majority_3CNF
begin

text \<open>
  Trust audit for the formalization of Gurumukhani et al., as in \<open>Audit\<close>: the build fails
  unless the headline theorems depend on no oracle (\<open>skip_proof\<close> from \<open>sorry\<close> or
  \<open>quick_and_dirty\<close>, or any other).
\<close>

ML \<open>
  val headline =
    [@{thm gkprst_bound}, @{thm gkprst_half}, @{thm IH_all},
     @{thm majority_mcnfs}, @{thm majority_mcnfs_exp},
     @{thm majority_mcnf_formula(1)}, @{thm majority_mcnf_formula(2)}];
  val oracles = Thm_Deps.all_oracles headline;
  val _ =
    if null oracles then writeln "AUDIT OK: headline theorems depend on no oracles"
    else error ("AUDIT FAILED: oracles " ^ @{make_string} oracles);
\<close>

end
