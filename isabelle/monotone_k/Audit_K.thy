theory Audit_K
  imports Harris_PPZ Shadow_Branch Deep_Payment Link_Gadget Private_Design Shearer_Sub Shearer_Entropy Shearer_Concentration Shearer_Certificate Shearer_Typical Shearer_Conditional Mirror_Payment Witness_Antichain Minterm_Cover
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
     @{thm group_bound}, @{thm ent_count}, @{thm ln_binom}, @{thm shearer_conc},
     @{thm gibbs}, @{thm geom_sum}, @{thm int_entropy}, @{thm certificate},
     @{thm int_entropy_typ}, @{thm certificate_typ}, @{thm int_entropy_dev}, @{thm certificate_dev},
     @{thm lent_image}, @{thm certificate_cond},
     @{thm mp_forces}, @{thm mp_mirror}, @{thm mp_tau}, @{thm mp_glue_tr}, @{thm mp_deficient},
     @{thm half_subsets}, @{thm mp_trace}, @{thm mp_count},
     @{thm lym}, @{thm sperner}, @{thm class_antichain}, @{thm card_traces},
     @{thm witness_bound}, @{thm witness_partition},
     @{thm minterm_mtr}, @{thm minterm_crit}, @{thm minterm_cover}, @{thm single_hit}, @{thm minterm_depth3},
     @{thm mtr_crit}, @{thm mtr_parts}];
  val oracles = Thm_Deps.all_oracles headline;
  val _ =
    if null oracles then writeln "AUDIT OK: headline theorems depend on no oracles"
    else error ("AUDIT FAILED: oracles " ^ @{make_string} oracles);
\<close>

end
