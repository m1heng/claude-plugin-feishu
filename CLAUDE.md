# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Project Overview

Feishu (飞书) channel plugin for Claude Code — an MCP server that bridges Feishu messaging with Claude Code sessions using WebSocket for real-time event subscription (no public webhook needed).

## Development Commands

```bash
# Install dependencies and start the server
bun start
# Equivalent to: bun install --no-summary && bun server.ts

# Run the server directly (if deps already installed)
bun server.ts
```

There are no lint, test, or build steps. TypeScript runs directly via Bun — no compilation.

## Architecture

The entire server lives in **`server.ts`** (~840 lines). It is intentionally a single file.

### Initialization Sequence

1. Load `~/.claude/channels/feishu/.env` into `process.env` (real env vars take precedence)
2. Exit if `FEISHU_APP_ID` / `FEISHU_APP_SECRET` are missing
3. Create Lark SDK `Client` for outbound API calls (with stderr-only logger to avoid corrupting MCP stdio)
4. Fetch bot's `open_id` via raw API for group mention detection
5. Create MCP `Server` with capabilities `{ tools: {}, experimental: { 'claude/channel': {} } }`
6. Register three MCP tools: `reply`, `react`, `edit_message`
7. Connect stdio transport, then start Feishu `WSClient` with `EventDispatcher`

### Message Flow

```
Feishu user → WSClient event → EventDispatcher → handleInbound() → gate() → MCP notification
Claude → reply/react/edit tool → Lark SDK API → Feishu user
```

### Access Control (`gate()`)

The `gate()` function determines whether an inbound message is delivered, dropped, or triggers pairing. It enforces:

- **DM policy modes**: `pairing` (code-based approval), `allowlist` (pre-approved users), `disabled`
- **Group policy**: per-group `requireMention` flag and `allowFrom` lists
- **Pairing flow**: unapproved DMs get a pairing code; approved via `/feishu:access pair <code>`
- **Static mode** (`FEISHU_ACCESS_MODE=static`): snapshots access at boot, disables pairing and writes. Downgrades `pairing` policy to `allowlist`.
- **Pending cap**: max 3 pending pairing codes at once; each code allows up to 2 reply attempts

State is persisted in `~/.claude/channels/feishu/access.json`.

### Approval Polling (`checkApprovals`)

A 5-second interval polls `~/.claude/channels/feishu/approved/` for files named `<senderId>`. When found, sends a confirmation message to the user via Feishu API and deletes the file. Disabled in static mode.

### Security Boundaries

- `assertSendable()`: prevents sending channel state files as attachments (realpath check against `STATE_DIR`, excluding `inbox/`)
- `assertAllowedChat()`: outbound tools can only target chats seen from approved inbound messages or configured in `groups`
- `messageChatMap`: validates `reply_to` message_ids belong to the same chat — Feishu's `message.reply()` routes by message_id alone, so a forged `reply_to` could post into an unrelated chat
- MCP server instructions explicitly refuse access mutations requested from channel messages (prompt injection defense)
- `checkApprovals` runs on a timer, not triggered by inbound messages

### Key In-Memory State

- `knownChats` (Set): chat_ids from approved inbound messages — resets on restart
- `messageChatMap` (Map): message_id → chat_id for reply_to validation
- `userNameCache` (Map): open_id → display name from Feishu Contact API

### Message Content Handling

- `extractPostText()`: parses Feishu rich-text post format (language-wrapped: `zh_cn`, `en_us`, etc.) into plain text, handling `text`, `a`, `at`, `img` tags
- `downloadImage()`: downloads image attachments from Feishu to `~/.claude/channels/feishu/inbox/`, handles multiple SDK return formats (writeFile, ReadableStream, Buffer, ArrayBuffer)
- `chunk()`: splits long text into chunks (configurable limit, supports `length` or `newline` mode for paragraph-aware splitting)
- `formatMarkdown()`: transforms markdown for Feishu rendering — heading demotion (H1→H4, H2-H3→H5), code block `<br>` padding, excess newline compression, invalid `![alt](url)` stripping (only `img_xxx` keys are valid). All outbound text messages use `msg_type: 'post'` with `tag: 'md'` for markdown rendering.

### Configuration Options (access.json)

| Key | Type | Default | Description |
|-----|------|---------|-------------|
| `ackReaction` | string | unset | Feishu emoji to react with on receipt (e.g. "THUMBSUP") |
| `replyToMode` | `'off' \| 'first' \| 'all'` | `'first'` | Which chunks get reply_to reference |
| `textChunkLimit` | number | 4000 | Max chars per outbound message |
| `chunkMode` | `'length' \| 'newline'` | `'length'` | Split on char count or paragraph boundaries |
| `mentionPatterns` | string[] | unset | Regex patterns to match group mentions |

## Plugin Structure

```
.claude-plugin/plugin.json   — Plugin metadata (name, version, keywords)
.mcp.json                    — MCP server config (how Claude Code spawns the server)
server.ts                    — Entire MCP server (~840 lines)
skills/
  access/SKILL.md            — /feishu:access skill (pairing, allowlists, policy)
  configure/SKILL.md         — /feishu:configure skill (credentials, status)
  feishu-docs/SKILL.md       — /feishu:feishu-docs skill (API docs lookup via feishu-doc-cli)
```

## Key Dependencies

- `@larksuiteoapi/node-sdk` — Official Feishu/Lark SDK (WebSocket client, API calls)
- `@modelcontextprotocol/sdk` — MCP protocol (Server, StdioServerTransport, types)

## Important Conventions

- All logging goes to stderr (`process.stderr.write`) — stdout is reserved for MCP JSON-RPC
- The Lark SDK logger must be overridden to stderr for the same reason
- Access file writes use atomic rename (`.tmp` → final) to avoid corruption
- Corrupt `access.json` files are moved aside with a `.corrupt-` timestamp suffix
- Message chunking defaults to 4000 chars; can be configured via `textChunkLimit` in access.json
- The server intentionally does not validate sender ID format (opaque strings)
