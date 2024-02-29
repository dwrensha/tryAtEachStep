# tryAtEachStep

`tryAtEachStep` is a tool that runs a tactic at every proof step in
a given Lean 4 file, reporting cases where the tactic closes the goal.

With a tactic like `exact?` and `rw_search`, this can help to
find ways in which your existing proofs can be improved.

## howto

Add this to your lakefile.lean:

```lean
require tryAtEachStep from git "https://github.com/dwrensha/tryAtEachStep"
```

Then do this:

```shell
$ lake exe tryAtEachStep exact? Foo/Bar.lean
```

## TODO

* Run in parallel on all `.lean` files in a project.
* Add tactic imports in input files. (Currently the input file needs know about the tactic.)
* Better handle situations where there are more than one active goal.
