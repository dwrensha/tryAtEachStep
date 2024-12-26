# tryAtEachStep

`tryAtEachStep` is a tool that runs a tactic at every proof step in
a given Lean 4 file, reporting cases where the tactic closes the goal.

With a tactic like `exact?` and `rw_search`, this can help to
find ways in which your existing proofs can be improved.

## howto

Add this to your lakefile.lean:

```lean
require tryAtEachStep from git "https://github.com/dwrensha/tryAtEachStep" @ "main"
```

Then do this:

```shell
$ lake exe tryAtEachStep exact? Foo/Bar.lean --outfile /tmp/out.json
```

Progress will be displayed via stderr as it happens.
Upon completion, `/tmp/out.json` will contain JSON describing the results.

### running on all files in a directory

The `tryAtEachStepInDirectory` tool runs `tryAtEachStep` on all `.lean` files
under a given directory. For example:

```shell
$ lake exe tryAtEachStepInDirectory "with_reducible exact?" YourLibrary -j 31
```

The `-j 31` argument specifies that 31 jobs should be run in parallel.

Results are written as JSON in a directory with name `tryAtEachStep-out-XXXXXXXX`,
where the X's get filled in randomly.
You can specify a different output directory via `--outdir`.


## Example findings:

* [mathlib#13335](https://github.com/leanprover-community/mathlib4/pull/13335)
* [mathlib#13334](https://github.com/leanprover-community/mathlib4/pull/13334)
* [mathlib#12715](https://github.com/leanprover-community/mathlib4/pull/12715)
* [mathlib#12678](https://github.com/leanprover-community/mathlib4/pull/12678)
* [mathlib#11093](https://github.com/leanprover-community/mathlib4/pull/11093)
* [mathlib@4900a2c5](https://github.com/leanprover-community/mathlib4/commit/4900a2c5b000492d1d0c6730f26d77a570b1a66c)
* [mathlib@866dfe56](https://github.com/leanprover-community/mathlib4/commit/866dfe56cc0541fbe0331ecacd1687bb99172f39)
* [mathlib@a6f77074](https://github.com/leanprover-community/mathlib4/commit/a6f770740f4c07b236c336115f4de99c28cd8910)
* [compfiles@cd250e72](https://github.com/dwrensha/compfiles/commit/cd250e726614a3c9ff60256da02db2c954d1dd8a)
* [compfiles@9a9eb697](https://github.com/dwrensha/compfiles/commit/9a9eb697ebf1bacd34ea4d4345686903d0dd0c22)
* [compfiles@0a02194e](https://github.com/dwrensha/compfiles/commit/0a02194eb3ce29f0d38e45a53e3f9943922c1398)
* [compfiles@22eaf558](https://github.com/dwrensha/compfiles/commit/22eaf558bd438ee11146c402ec4db9533404df58)
* [compfiles@8ee4ce58](https://github.com/dwrensha/compfiles/commit/8ee4ce58c3309ba73a466bd5db7817d68844ca9d)
* [compfiles@8fd2ff0a](https://github.com/dwrensha/compfiles/commit/8fd2ff0a3ca8f5d6b9fcc2650a0c3f4220ec0f5f)
* [compfiles@fdf0f9a0](https://github.com/dwrensha/compfiles/commit/fdf0f9a03db591897e91b17a9772b916bfd2cd67)
* [compfiles@b8068381](https://github.com/dwrensha/compfiles/commit/b80683817ccd3f7d52d877b9cff5c687ac0f940a)
* [compfiles@f76ad21b](https://github.com/dwrensha/compfiles/commit/f76ad21bf9888f290dbbdc748939c4c8427f34a9)
* [compfiles@8650fb4a](https://github.com/dwrensha/compfiles/commit/8650fb4ad67533e269aecb73c3d36fe5226f6dee)
* [compfiles@fe99e1e9](https://github.com/dwrensha/compfiles/commit/fe99e1e9c1f991d338a7d97b25e2ab1002bac30f)
* [compfiles@6c3272cb](https://github.com/dwrensha/compfiles/commit/6c3272cbbed145ed5a9451ada5b14139e898177a)

## TODO

* Tests
* Support tactics that aren't imported by the input file.
* Better handling of situations where there are multiple active goals.
* Report performance statistics of existing and new tactic.
* Operate on terms. (Currently only operates on the tactic steps of the given file.)
