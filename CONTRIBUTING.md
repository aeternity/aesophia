# Contributing to Sophia

## Checklist For Creating New Pull Requests

The following points should be considered before creating a new PR to the Sophia compiler.

### Documentation

- The [Changelog](CHANGELOG.md) file should be updated for all PRs.
- If a PR introduces a new feature that is relevant to the users of the language, the [Sophia Features Documentation](docs/sophia_features.md) should be updated to describe the new feature.
- If a PR introduces new syntax (e.g. changes in [aeso_syntax.erl](src/aeso_syntax.erl), [aeso_scan.erl](src/aeso_scan.erl), or [aeso_parser.erl](src/aeso_parser.erl)), the [Sophia Syntax Documentation](docs/sophia_syntax.md) should be updated to include the new syntax.
- If a PR introduces a new library, the public interface of the new library should be fully documented in the [Sophia Standard Library Documentation](docs/sophia_stdlib.md).
- If a PR introduces a new compiler option, the new option should be documented in the file
[aeso_compiler.md](docs/aeso_compiler.md).

### Tests

- If a PR introduces new syntax (e.g. changes in [aeso_syntax.erl](src/aeso_syntax.erl), [aeso_scan.erl](src/aeso_scan.erl), or [aeso_parser.erl](src/aeso_parser.erl)), the contract [all_syntax.aes](test/contracts/all_syntax.aes) should be updated to include the new syntax.
- If a PR fixes a bug, the code that replicates the bug should be added as a new passing test contract.
- If a PR introduces a new feature, add tests for both successful and failing usage of that feature. In order to run the entire compilation pipeline and to avoid erroring during intermediate steps, failing tests should not be mixed with the successful ones.

### Source Code

- If a PR introduces new syntax (e.g. changes in [aeso_syntax.erl](src/aeso_syntax.erl), [aeso_scan.erl](src/aeso_scan.erl), or [aeso_parser.erl](src/aeso_parser.erl)), the following code should be updated to handle the new syntax:
    - The function `aeso_syntax_utils:fold/4` in the file [aeso_syntax_utils.erl](src/aeso_syntax_utils.erl).
    - Any related pretty printing function in the file [aeso_pretty.erl](src/aeso_pretty.erl), depending on the type of the newly added syntax.

## Checklist For Creating a Release

- Update the version in the file [aesophia.app.src](src/aesophia.app.src).
- Update the version in the file [rebar.config](rebar.config).
- In the [Changelog](CHANGELOG.md):
    - Update the `Unreleased` changes to be under the new version.
    - Update the version at the bottom of the file.
- Commit and the changes and create a new PR (check the commit of [v6.1.0](https://github.com/aeternity/aesophia/commit/5ad5270e381f6e810d7b8b5cdc168d283e7a90bb) for reference).
- Create a release after merging the new PR to `master` branch.
- After releasing `aesophia`, refer to each of the following repositories and create new releases as well, using the new `aesophia` release:
    - [aesophia_cli](https://github.com/aeternity/aesophia_cli)
    - [aesophia_http](https://github.com/aeternity/aesophia_http)
    - [aerepl](https://github.com/aeternity/aerepl)
