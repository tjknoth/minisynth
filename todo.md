# Various TODOs
* Add error monad
* add holes
* add any types?
* write constraint solver
* write direct synthesizer
* write indirect synthesizer

## Notes on tasks
* direct/indirect synthesizer use different typechecker styles 
* (ie, round-trip vs holes)
* this is a bit awkward, since typing judgments should ideally be different
* maybe I should write two different typecheckers?
* would be the "purest"
* direct synthesizer (round-trip):
  * need hole types, not holes
  * need typechecking everywhere
* indirect synthesizer
  * need holes, not hole types