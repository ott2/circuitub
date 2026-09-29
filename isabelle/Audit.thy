theory Audit
  imports Majority_Circuits
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
     @{thm symmetric_functions_big_O}, @{thm majority_circuits}, @{thm majority_depth3}];
  val oracles = Thm_Deps.all_oracles headline;
  val _ =
    if null oracles then writeln "AUDIT OK: headline theorems depend on no oracles"
    else error ("AUDIT FAILED: oracles " ^ @{make_string} oracles);
\<close>

end
