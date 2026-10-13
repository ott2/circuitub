theory Audit_K
  imports Cluster_PPZ
begin

text \<open>
  Trust audit for the monotone \<open>k\<close> work, as in \<open>Audit\<close>: the build fails unless the headline
  theorems depend on no oracle (\<open>skip_proof\<close> from \<open>sorry\<close> or \<open>quick_and_dirty\<close>, or any other).
\<close>

ML \<open>
  val headline =
    [@{thm sum_PiE_split}, @{thm sum_PiE_prod_ge}, @{thm cluster_sum}, @{thm cluster_count}];
  val oracles = Thm_Deps.all_oracles headline;
  val _ =
    if null oracles then writeln "AUDIT OK: headline theorems depend on no oracles"
    else error ("AUDIT FAILED: oracles " ^ @{make_string} oracles);
\<close>

end
