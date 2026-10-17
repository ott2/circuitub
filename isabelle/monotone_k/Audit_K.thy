theory Audit_K
  imports Harris_PPZ Shadow_Branch Deep_Payment Link_Gadget Private_Design Shearer_Sub Shearer_Entropy Shearer_Concentration
begin

text \<open>
  Trust audit for the monotone \<open>k\<close> work, as in \<open>Audit\<close>: the build fails unless the headline
  theorems depend on no oracle (\<open>skip_proof\<close> from \<open>sorry\<close> or \<open>quick_and_dirty\<close>, or any other).
\<close>

ML \<open>
  val headline =
    [@{thm sum_PiE_split}, @{thm sum_PiE_prod_ge}, @{thm cluster_sum}, @{thm cluster_count},
     @{thm harris}, @{thm harris_prod}, @{thm harris_count}, @{thm gav_single}, @{thm gav_cluster},
     @{thm cluster_count_overlap}, @{thm harris_ppz_r}, @{thm harris_ppz},
     @{thm minimal_branch}, @{thm shadow_branch},
     @{thm dp_forces}, @{thm dp_tau}, @{thm dp_normal(1)}, @{thm dp_normal(2)}, @{thm dp_count},
     @{thm link_rank}, @{thm link_mint}, @{thm link_count}, @{thm proj_slack(1)}, @{thm proj_slack(2)},
     @{thm private_design}, @{thm three_blocks}, @{thm half_blocks},
     @{thm shearer_sub}, @{thm ent_empty}, @{thm ent_full}, @{thm ent_mono}, @{thm count_bound},
     @{thm ent_sub}, @{thm shearer_ent},
     @{thm group_bound}, @{thm ent_count}, @{thm ln_binom}, @{thm shearer_conc}];
  val oracles = Thm_Deps.all_oracles headline;
  val _ =
    if null oracles then writeln "AUDIT OK: headline theorems depend on no oracles"
    else error ("AUDIT FAILED: oracles " ^ @{make_string} oracles);
\<close>

end
