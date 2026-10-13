theory Audit_K
  imports Harris_PPZ
begin

text \<open>
  Trust audit for the monotone \<open>k\<close> work, as in \<open>Audit\<close>: the build fails unless the headline
  theorems depend on no oracle (\<open>skip_proof\<close> from \<open>sorry\<close> or \<open>quick_and_dirty\<close>, or any other).
\<close>

ML \<open>
  val headline =
    [@{thm sum_PiE_split}, @{thm sum_PiE_prod_ge}, @{thm cluster_sum}, @{thm cluster_count},
     @{thm harris}, @{thm harris_prod}, @{thm harris_count}, @{thm gav_single}, @{thm gav_cluster},
     @{thm cluster_count_overlap}, @{thm harris_ppz_r}, @{thm harris_ppz}];
  val oracles = Thm_Deps.all_oracles headline;
  val _ =
    if null oracles then writeln "AUDIT OK: headline theorems depend on no oracles"
    else error ("AUDIT FAILED: oracles " ^ @{make_string} oracles);
\<close>

end
