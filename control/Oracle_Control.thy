theory Oracle_Control
  imports Complex_Main
begin

text \<open>Positive control for the oracle audit: a sorried lemma must be detected.\<close>

lemma bogus: "False" sorry

ML \<open>
  val oracles = Thm_Deps.all_oracles [@{thm bogus}];
  val _ =
    if null oracles then error "CONTROL FAILED: sorry not detected"
    else writeln ("CONTROL OK: detected " ^ @{make_string} oracles);
\<close>

end
