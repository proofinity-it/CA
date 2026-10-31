# node-mcp: a CA live node as an MCP tool

One tool, `ca_lookup`, for an agent that writes Lean: before proving a
statement, ask a CA node whether Mathlib, Lean Pool or Tau Ceti already
states it, under whatever name. It wraps the node's one URL
(`/q?s=…&format=json`, see https://node.proofinity.it/llms.txt) and
returns the answer as data: the address, the declarations and the pool
theorems stating it.

Exact matches only: the same term up to bound-variable and universe
names. Hypotheses in another order or a changed binder give another
address, so no match means "not stated this way", never "unproved".

## Run

One file, one dependency (`mcp`), installed by `uv` on first use:

```sh
uv run tools/node-mcp/ca_node_mcp.py          # stdio; waits for a client
```

Claude Code:

```sh
claude mcp add canode -- uv run /absolute/path/to/ca_node_mcp.py
```

Any other MCP client: command `uv`, arguments `run
/absolute/path/to/ca_node_mcp.py`, transport stdio. `CA_NODE_URL` points
it at another node (default `https://node.proofinity.it`).

What you ask leaves your machine: each query is one HTTPS request to
the node, which answers about ten statements a minute per client, one
to three seconds each, and stores nothing of what is sent. Nothing else
is sent, and nothing runs locally but this file and the MCP SDK.
