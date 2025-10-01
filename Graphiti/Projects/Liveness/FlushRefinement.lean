-- What we want to do:
-- · Define flushability property on trace
-- · Say that we have a specification module on which flushability is true
-- · Assume the liveness_refinement between specification module and our module
-- · Show that this implies flushability on our implementation module
-- We could then try to exhibit such a specification module and try to prove the
-- property on it, and then prove the refinement.

import Graphiti.Core.ModuleLemmas
import Graphiti.Core.StateTransition
import Graphiti.Core.Trace
import Graphiti.Projects.Liveness.ComposedModule
