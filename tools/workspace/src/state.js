export const scenarios = {
  connected: {
    label: "Valid reaction",
    description:
      "Two admitted members in the same community. Shared ops travel through a controlled delivery queue.",
    present: 1,
    valid: 1,
    member: 1,
    same: 1,
  },
  missing: {
    label: "Dependency arrives later",
    description:
      "Rowan receives a reaction before its message. It must wait until the authorizing dependency arrives.",
    present: 0,
    valid: 1,
    member: 1,
    same: 1,
  },
  foreign: {
    label: "A cross-community reference",
    description:
      "A valid message exists, but belongs to another community. Availability alone does not authorize this reference.",
    present: 1,
    valid: 1,
    member: 1,
    same: 0,
  },
  invalid: {
    label: "Invalid parent message",
    description:
      "The dependency has arrived but was rejected. The reaction must not become visible.",
    present: 1,
    valid: 0,
    member: 1,
    same: 1,
  },
  outsider: {
    label: "An unauthorized author",
    description:
      "The simulated author has no membership fact. The fixture does not model cryptographic signatures.",
    present: 1,
    valid: 1,
    member: 0,
    same: 1,
  },
};
export function initialState(saved = {}) {
  return {
    scenario: "connected",
    paused: false,
    osDark: 0,
    clients: [
      {
        name: "Maya",
        preference: saved.maya ?? 0,
        reactions: 1,
        draft: "",
        messages: [],
      },
      {
        name: "Rowan",
        preference: saved.rowan ?? 2,
        reactions: 1,
        draft: "",
        messages: [],
      },
    ],
    queue: [],
    selectedClient: 0,
    selectedOp: "reaction:3f8a",
    log: [],
    sequence: 0,
    sourceDraft: "",
    definitionDrafts: {},
    selectedEmoji: "🌱",
    emojiSearch: "",
    proofDrafts: {},
    gameLevel: 0,
    shellDark: false,
    accent: 0x0969da,
    ...saved,
  };
}
export function verdict(state, kernel) {
  const s = scenarios[state.scenario];
  return kernel.quiet_validate(
    s.present,
    s.valid,
    s.member,
    s.same,
    1, // The browser always uses the checked policy.
  );
}
export function act(state, action, kernel) {
  const s = structuredClone(state);
  const log = (text, kind = "event") =>
    s.log.unshift({ id: ++s.sequence, text, kind });
  switch (action.type) {
    case "scenario":
      s.scenario = action.value;
      s.queue = [];
      s.clients.forEach((c) => {
        c.reactions = 1;
        c.messages = [];
      });
      log(`Loaded fixture · ${scenarios[s.scenario].label}`);
      break;
    case "react": {
      const v = verdict(s, kernel);
      if (v !== 1) {
        log(
          v === 0
            ? "Reaction waiting · message dependency unavailable"
            : "Reaction rejected",
          v === 0 ? "wait" : "reject",
        );
        break;
      }
      const i = action.client;
      s.clients[i].reactions++;
      const delivery = {
        id: ++s.sequence,
        type: "reaction",
        from: i,
        to: 1 - i,
      };
      if (s.paused) {
        s.queue.push(delivery);
        log(
          `${s.clients[i].name} created reaction · queued for ${s.clients[1 - i].name}`,
        );
      } else {
        s.clients[1 - i].reactions++;
        log(
          `Reaction accepted · delivered to ${s.clients[1 - i].name}`,
          "accept",
        );
      }
      break;
    }
    case "send": {
      const c = s.clients[action.client];
      const text = c.draft.trim();
      if (!text) break;
      c.messages.push(text);
      c.draft = "";
      if (s.paused)
        s.queue.push({
          id: ++s.sequence,
          type: "message",
          text,
          to: 1 - action.client,
        });
      else s.clients[1 - action.client].messages.push(text);
      log(`${c.name} sent a fixture message`, "accept");
      break;
    }
    case "deliver": {
      const d = s.queue.shift();
      if (d) {
        if (d.type === "reaction") s.clients[d.to].reactions++;
        else s.clients[d.to].messages.push(d.text);
        log(`Delivered ${d.type} to ${s.clients[d.to].name}`, "accept");
      }
      break;
    }
    case "pause":
      s.paused = !s.paused;
      log(
        s.paused
          ? "Transport paused · new deliveries will queue"
          : "Transport resumed · queued deliveries remain under your control",
      );
      break;
    case "resolve":
      s.scenario = "connected";
      log(
        "Message dependency delivered · waiting reaction can now validate",
        "accept",
      );
      break;
    case "theme":
      s.clients[action.client].preference = Number(action.value);
      log(
        `${s.clients[action.client].name} appearance · ${["system", "light", "dark"][action.value]}`,
      );
      break;
    case "os":
      s.osDark = 1 - s.osDark;
      log(`Host appearance · ${s.osDark ? "dark" : "light"}`);
      break;
    case "draft":
      s.clients[action.client].draft = action.value;
      break;
    case "client":
      s.selectedClient = action.client;
      break;
    case "accent":
      s.accent = action.value;
      break;
    case "emoji":
      s.selectedEmoji = action.value;
      break;
    case "emoji-search":
      s.emojiSearch = action.value;
      break;
    case "definition":
      s.definitionDrafts[action.name] = action.value;
      break;
    case "source":
      s.sourceDraft = action.value;
      break;
  }
  s.log = s.log.slice(0, 40);
  return s;
}
