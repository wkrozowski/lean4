/-
Tests for the `deprecated_module` command.
-/

-- Missing both message and since
/--
warning: `deprecated_module` should specify a deprecation message
---
warning: `deprecated_module` should specify the date or library version at which the deprecation was introduced, using `(since := "...")`
-/
#guard_msgs in
deprecated_module

-- Missing since only (also warns about duplicate since module is already marked above)
/--
warning: module is already marked as deprecated
---
warning: `deprecated_module` should specify the date or library version at which the deprecation was introduced, using `(since := "...")`
-/
#guard_msgs in
deprecated_module "use NewModule instead"

-- Missing message only (also warns about duplicate)
/--
warning: module is already marked as deprecated
---
warning: `deprecated_module` should specify a deprecation message
-/
#guard_msgs in
deprecated_module (since := "2026-03-19")

-- Both message and since: only duplicate warning
/--
warning: module is already marked as deprecated
-/
#guard_msgs in
deprecated_module "use NewModule instead" (since := "2026-03-19")

-- Duplicate deprecated_module: warns about already being marked (standalone confirmation)
/--
warning: module is already marked as deprecated
-/
#guard_msgs in
deprecated_module "use SomethingElse instead" (since := "2026-03-20")
