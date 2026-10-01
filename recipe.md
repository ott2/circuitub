# circuitub

## Session 1

### Prompt 1.1

Here we are looking at a recent paper that claims to resolve the bounded-depth circuit complexity of Majority, by using a general upper bound for symmetric functions that match Håstad's lower bound for Parity. Please take a look and deliver a grounded verdict: ideally this should be done by producing a counterexample in Lean or Isabelle (or LADR Mace4 or Vampire, if ATPs are suitable here), or a verified proof. If you use Isabelle, please install the PyPI commandline tools isabelle-watchdog and isabelle-query that have been greatly useful in our Isabelle projects. Please try to make significant progress without asking me for feedback overnight.

### Prompt 1.2

/model

### Prompt 1.3

Here we are looking at a recent paper that claims to resolve the bounded-depth circuit complexity of Majority, by using a general upper bound for symmetric functions that match Håstad's lower bound for Parity. Please take a look and deliver a grounded verdict: ideally this should be done by producing a counterexample in Lean or Isabelle (or LADR Mace4 or Vampire, if ATPs are suitable here), or a verified proof. If you use Isabelle, please install the PyPI commandline tools isabelle-watchdog and isabelle-query into a fresh venv as these have been greatly useful in our Isabelle projects. Please try to make significant progress without asking me for feedback overnight. Keep work here rather than in /tmp, please.

### Prompt 1.4

Here we are looking at a recent paper that claims to resolve the bounded-depth circuit complexity of Majority, by using a general upper bound for symmetric functions that match Håstad's lower bound for Parity. Please take a look and deliver a grounded verdict: ideally this should be done by producing a counterexample in Lean or Isabelle (or LADR Mace4 or Vampire, if ATPs are suitable here), or a verified proof. If you use Isabelle, please install the PyPI commandline tools isabelle-watchdog and isabelle-query into a fresh venv as these have been greatly useful in our Isabelle projects. Please try to make significant progress without asking me for feedback overnight. Keep work here rather than in /tmp, please. I don't think running multi-year combinatorial searches in Python is going to help -- circuit complexity deals with a number of objects where nearly everything is too large to check experimentally.

### Prompt 1.5

/model

### Prompt 1.6

Here we are looking at a recent paper that claims to resolve the bounded-depth circuit complexity of Majority, by using a general upper bound for symmetric functions that match Håstad's lower bound for Parity. Please take a look and deliver a grounded verdict: ideally this should be done by producing a counterexample in Lean or Isabelle (or LADR Mace4 or Vampire, if ATPs are suitable here), or a verified proof. If you use Isabelle, please install the PyPI commandline tools isabelle-watchdog and isabelle-query into a fresh venv as these have been greatly useful in our Isabelle projects. Please try to make significant progress without asking me for feedback overnight. Keep work here rather than in /tmp, please. I don't think running multi-year combinatorial searches in Python is going to help -- circuit complexity deals with a number of objects where nearly everything is too large to check experimentally.

### Prompt 1.7

The AFP is available locally in ~/repos/afp although it is checked out at the 2025-2 tag rather than the latest due to some Scala code in a recent entry that breaks in Isabelle2025-2.

### Prompt 1.8

Please use smaller timeouts; the point of the watchdog is to waste less time waiting on infinite loops to hit the timeout.

### Prompt 1.9

At this point we should probably see a verdict within 40s (when the proof grows larger this might need to increase).

### Prompt 1.10

Please also drop the tail on the isabelle-build output; it already summarises and truncates long output and the most important part of its output is the first few lines.

### Prompt 1.11

The complex bash calls you are making (there is no need to keep changing directory, CWD is fine) are causing the classifier to decide we are running some kind of underhand operation and degrading our work; please use the standard edit tool if making simple edits, and rather use simpler forms of tool calls.

### Prompt 1.12

/model

### Prompt 1.13

Excellent, thank you. Does our modified construction work for any symmetric function, or only for Majority?

### Prompt 1.14

Thank you. Based on the style of exposition in the arXiv paper, please write a LaTeX document that explains what has been proved in Isabelle, with a section that explains how our approach differs from Lecomte-Ramakrishnan.

### Prompt 1.15

Great, please commit and push this (I've set up the remote).

### Prompt 1.16

It's private for now.

## Session 2 (context compacted)

### Prompt 2.1

Astra formalised the result in Lean in @~/repos/warrants/complexitylib/Complexitylib/Circuits/Shallow.lean as prompted by Sam Schlesinger. Does this warrant demonstrate the same result we formalised?

### Prompt 2.2

Lean is available if you wanted to investigate, but that's probably not necessary (I believe the proof verifies).

### Prompt 2.3

It sounds to me like our strict layering is more restrictive than their depth at most d. Is that right?

### Prompt 2.4

I think we should make the repo public, and email the authors that this has been done -- they might want to do their own formalisation or mention ours as a footnote. This means removing their paper from the committed files; please let me know what git history rewriting needs to be done (the classifier disallows rewriting so I have to do this manually).

### Prompt 2.5

Thanks, could you write those steps as a .sh file I could tweak?

### Prompt 2.6

OK, that worked but I realised the trajectories are still in the project history (I moved these out); these contain some mildly private details of this machine and our local paths. Please remove those from git history as well; I have set up an empty github repo again.

### Prompt 2.7

t/ disappeared, it had the symlink to the trajectories only (we usually do the Isabelle theories in t/ but no matter).

### Prompt 2.8

It is public already; I have already written an email. However, please write a short README.me so the github repo isn't blank.

### Prompt 2.9

Please add a full attribution for yourself to the bottom of the README; I acted as editor here.

### Prompt 2.10

Perfect, thank you.
