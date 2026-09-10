-- General-purpose material with no Datalog content: lists, sets, strings,
-- and abstract rewriting. Kept apart so the Datalog development can be read
-- without it, and so this repo stands alone without a library dependency.
--
-- Importing this root brings in all of it; the Datalog modules instead
-- import only the pieces they need, which keeps the layering visible.

import LeanDatalog.Utils.List
import LeanDatalog.Utils.Set
import LeanDatalog.Utils.String
import LeanDatalog.Utils.Relation
