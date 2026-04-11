# claude-channel-feishu

Feishu (飞书) channel plugin for [Claude Code](https://claude.com/claude-code) — receive and reply to Feishu messages directly in your terminal.

## Prerequisites

- [Claude Code](https://claude.com/claude-code) v2.1.80+
- [Bun](https://bun.sh) runtime
- A Feishu self-built app with Bot capability ([setup guide](#create-a-feishu-app))

## Install

```bash
# Add the marketplace (one-time)
claude plugin marketplace add haojunyu/claude-plugins

# Install the plugin
claude plugin install feishu@haojunyu-plugins
```

## Configure

### Create a Feishu app

1. Go to [Feishu Open Platform](https://open.feishu.cn/app) > Create App > Enterprise Self-Built App
2. Enable **Bot** capability
3. Add permissions (scopes):
   - `im:message` — send and receive messages
   - `im:message:send_as_bot` — send as bot
   - `im:resource` — upload images and files
   - `im:message.reactions:write_only` — add reactions (optional)
4. In **Events & Callbacks** > **Event Configuration**:
   - Select **"Use persistent connection to receive events"** (使用长连接接收事件)
   - Subscribe to event: `im.message.receive_v1`
5. Publish the app version and wait for admin approval
6. Copy **App ID** and **App Secret** from Credentials & Basic Info

### Save credentials

In Claude Code, run:

````
/feishu:configure <app_id> <app_secret>
```

### Start with channels

```bash
freecode --channels plugin:feishu@m1heng-plugins
```

### Pair your Feishu account

1. DM your bot on Feishu — it replies with a pairing code
2. In Claude Code, run `/feishu:access pair <code>` to approve

## Skills

| Skill | Description |
|---|---|
| `/feishu:configure` | Save credentials, check channel status |
| `/feishu:access` | Manage pairing, allowlists, DM/group policy |
| `/feishu:feishu-docs` | Look up Feishu Open Platform API docs |

## How it works

The plugin runs a local MCP server that connects to Feishu via WebSocket (persistent connection). No public webhook URL needed. Messages from allowed senders are forwarded to your Claude Code session; Claude can reply, react, and send files back through the channel.

## License

MIT
