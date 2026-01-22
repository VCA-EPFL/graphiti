/-
Copyright (c) 2025 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gurvan Debaussart
-/

import Graphiti.Projects.Noc.Utils
import Graphiti.Projects.Noc.Lang

namespace Graphiti.Projects.Noc

  variable {netsz : Netsz}

  theorem mkDir_isConn_out {t : Topology netsz} rid i h:
    t.isConnDir_out (t.mkDir_out rid i h) := by
      simp [Topology.mkDir_out]

  theorem mkDir_isConn_inp {t : Topology netsz} rid i h:
    t.isConnDir_inp (t.mkDir_inp rid i h) := by
      simp [Topology.mkDir_inp]

  theorem conns_isConn_out {t : Topology netsz} {conn} (Hconn : conn ∈ t.conns) :
    t.isConnDir_out conn.1.2 := by
      sorry

  theorem conns_isConn_inp {t : Topology netsz} {conn} (Hconn : conn ∈ t.conns) :
    t.isConnDir_inp conn.2.2 := by
      sorry

  -- TODO:
  -- Prove correctness of Topology.conns by having the fact that
  -- conn ∈ t.conns → getConnDir_out (conn_is_conn_out H) = conn.2.1
  theorem conns_getConnDir_out {t : Topology netsz} {conn} (Hconn : conn ∈ t.conns) :
    t.getConnDir_out (conns_isConn_out Hconn) = conn.2.1 := by
      sorry

  -- TODO
  -- theorem conns_getConnDir_inp {t : Topology netsz} {conn} (Hconn : conn ∈ t.conns) :
  --   t.getConnDir_inp (conns_isConn_inp Hconn) = conn.1.1 := by
  --     sorry

end Graphiti.Projects.Noc
