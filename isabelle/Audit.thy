theory Audit
  imports Block_Local Monotone_Mixed
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
     @{thm matching_valid}, @{thm matching_card}, @{thm matching_weight}];
  val oracles = Thm_Deps.all_oracles headline;
  val _ =
    if null oracles then writeln "AUDIT OK: headline theorems depend on no oracles"
    else error ("AUDIT FAILED: oracles " ^ @{make_string} oracles);
\<close>

end
