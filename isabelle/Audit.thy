theory Audit
  imports Block_Local Monotone_Mixed Monotone_Formula Depth3_Lower
begin

text \<open>
  Trust audit.  \<open>Thm_Deps.all_oracles\<close> collects every oracle (e.g. \<open>skip_proof\<close>, produced by
  \<open>sorry\<close> or \<open>quick_and_dirty\<close>) that a theorem's derivation depends on.  The build fails
  unless the list is empty, i.e. unless the headline theorems are derived purely by the
  Isabelle/HOL kernel from the axioms of HOL.
\<close>

ML \<open>
  val headline =
    [@{thm symmetric_upper_bound}, @{thm symmetric_functions},
     @{thm symmetric_functions_big_O}, @{thm majority_circuits}, @{thm majority_depth3},
     @{thm symmetric_or_of_cnfs}, @{thm symmetric_or_of_cnfs_width},
     @{thm majority_or_of_cnfs}, @{thm enum_output_lower_bound},
     @{thm symmetric_or_of_cnfs_local}, @{thm one_block_tests}, @{thm one_block_tests_equal},
     @{thm test_valid}, @{thm valid_test(1)}, @{thm valid_test(2)}, @{thm valid_test(3)},
     @{thm exchange}, @{thm determination},
     @{thm pairwise_count}, @{thm pairwise_weight}, @{thm three_blocks},
     @{thm free_determined}, @{thm free_small}, @{thm sharp_bounds(1)}, @{thm sharp_bounds(2)},
     @{thm clause_per_maxfalse}, @{thm pair_cost}, @{thm test_cost}, @{thm slice_count},
     @{thm tests_needed},
     @{thm tfree_determined}, @{thm tfree_small}, @{thm tight_compress}, @{thm mixed_tight},
     @{thm mixed_weight}, @{thm mixed_cover}, @{thm tight_cost},
     @{thm hfree_determined}, @{thm good_colorings}, @{thm average_free},
     @{thm hyper_sound_tight}, @{thm hyper_lower_nontight}, @{thm hyper_compress},
     @{thm wdec_eq}, @{thm wfree_determined}, @{thm max_false}, @{thm wide_maxfalse},
     @{thm wide_cost}, @{thm wide_compress}, @{thm wide_cover}, @{thm wide_good},
     @{thm hyper_good}, @{thm kraft_partial}, @{thm power_average}, @{thm kraft_count},
     @{thm wide_kraft}, @{thm wide_cover_kraft}, @{thm hyper_kraft},
     @{thm central_binomial}, @{thm central_ratio}, @{thm slice_lower}, @{thm binomial_moment},
     @{thm chebyshev_window}, @{thm window_range}, @{thm window_lower}, @{thm window_beta},
     @{thm decoded_fraction},
     @{thm tw_cnf}, @{thm tw_sound}, @{thm formula_kraft}, @{thm atypical_count},
     @{thm typical_half}, @{thm majority_wide_tests}, @{thm majority_wide_size}, @{thm beta_log},
     @{thm window_d}, @{thm beta_half}, @{thm majority_wide_explicit},
     @{thm forced_kraft}, @{thm ppz_count}, @{thm crit_count}, @{thm sigma3_slice},
     @{thm sigma3_threshold}, @{thm majority_depth3_lower}, @{thm majority_depth3_sqrt},
     @{thm majority_cnfs_lower}, @{thm majority_cnfs_lower_e},
     @{thm matching_valid}, @{thm matching_card}, @{thm matching_weight}];
  val oracles = Thm_Deps.all_oracles headline;
  val _ =
    if null oracles then writeln "AUDIT OK: headline theorems depend on no oracles"
    else error ("AUDIT FAILED: oracles " ^ @{make_string} oracles);
\<close>

end
