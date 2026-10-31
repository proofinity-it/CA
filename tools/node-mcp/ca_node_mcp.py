# /// script
# requires-python = ">=3.10"
# dependencies = ["mcp>=1.2"]
# ///
"""An MCP server for a CA live node: one tool, `ca_lookup`.

Give it a Lean 4 statement (as written after `theorem _ :`, Mathlib open),
a Mathlib name or an address; it asks the node and returns the answer as
JSON: the address, and the declarations and Lean Pool theorems that
state it. Exact matches only (see the node's /llms.txt).

Run it (uv installs the one dependency on first use):

    uv run tools/node-mcp/ca_node_mcp.py

Claude Code:

    claude mcp add canode -- uv run /path/to/ca_node_mcp.py

Any MCP client: command `uv`, args `run /path/to/ca_node_mcp.py`,
transport stdio. CA_NODE_URL points it at another node.
"""
import json, os, urllib.parse, urllib.request, urllib.error
try:                                                  # mcp 2.x
    from mcp.server.mcpserver import MCPServer as FastMCP
except ImportError:                                   # mcp 1.x
    from mcp.server.fastmcp import FastMCP

NODE = os.environ.get("CA_NODE_URL", "https://node.proofinity.it").rstrip("/")
mcp = FastMCP("canode", instructions=(
    "A CA live node: content addresses of every theorem in Mathlib, Lean Pool and Tau Ceti. "
    "Use ca_lookup before proving a statement, to see whether one of them already states it exactly. "
    "A statement is written as after `theorem _ :` in Lean 4 with Mathlib open."))


@mcp.tool()
def ca_lookup(query: str) -> dict:
    """Ask the node whether a statement is already proved, under whatever name.

    `query` is a Lean 4 statement (as after `theorem _ :`, Mathlib open, e.g.
    `∀ n : ℕ, n + 0 = n`), a Mathlib name (e.g. `Nat.add_zero`) or a CA
    address. The answer has `status` ("ok", "error" for a statement Lean
    could not read, "not_found" for an unknown name or address), `stmt`
    (the address), `type` (what Lean read), `mathlib` (declarations with
    this statement: name, kind, module) and `lean_pool` (project and
    theorem; project "TauCeti" is Tau Ceti). Matches are exact: the same
    term up to bound-variable and universe names. Hypotheses in another
    order or a changed binder give another address, so no match means
    "not stated this way", never "unproved". About ten statements a
    minute; one to three seconds each. The query is sent to the node
    over HTTPS and not stored there.
    """
    q = query.strip()
    if not q:
        return {"status": "error", "error": "empty query"}
    url = f"{NODE}/q?s={urllib.parse.quote(q)}&format=json"
    req = urllib.request.Request(url, headers={"User-Agent": "ca-node-mcp/1 (+https://github.com/proofinity-it/CA)"})
    try:
        with urllib.request.urlopen(req, timeout=60) as r:   # follows the 303 to the right answer
            d = json.loads(r.read().decode())
            if "names" in d:                                  # a dotted name the node does not bind: a search
                d["status"] = "not_found" if not d["names"] else "ok"
                d["note"] = "not a known name; `names` are the closest Mathlib names, each with its address"
            return d
    except urllib.error.HTTPError as e:
        try:
            return json.loads(e.read().decode())             # 422 / 404 carry the answer as JSON too
        except Exception:
            return {"status": "error", "error": f"HTTP {e.code} from the node"}
    except Exception as e:
        return {"status": "error", "error": f"the node did not answer: {type(e).__name__}: {e}"}


if __name__ == "__main__":
    mcp.run()
