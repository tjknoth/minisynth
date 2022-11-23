# minisynth 
Minimal examples of performance issues with different approaches to logic programming in haskell
(using program synthesis as an example)

### Synthesis paradigms
We compare two approaches: _direct_ and _indirect_.
In the direct style, the synthesizer is embedded in the typechecker (src/RoundTrip.hs).
Upon encountering a hole, the round-trip typechecker (and synthesizer) guesses a term.

In the indirect style, the typechecker simply annotates holes with specifications (a tuple
of a typing context and a goal type).
Then, a separate synthesis module handles the process of filling the hole.
Filling a hole will require calling back into the typechecker 
in order to generate specifications
for any new subgoals.


### Direct style:
Implemented in `src/RoundTrip.hs`, the direct synthesizer just re-uses
the typechecking logic but adds non-determinism.

### Indirect style:
Implemented in `src/Synthesizer.hs`, the indirect synthesizer uses
the typechecker (in `src/Gradual.hs`) to _annotate_ each term.
Then, it solves sub-goals according to the specifications produced by the typechecker.

### Running the synthesizer
The CLI is very dumb. Usage:
`stack exec -- minisynth [style]` where "style" is either "direct" or "indirect".
Then, the executable solves whatever benchmark is hard-coded into `bin/Main.hs`