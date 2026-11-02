import type { Meta, StoryObj } from '@storybook/svelte-vite'
import Window from './design/Window.svelte'
import { harness, turnedFrom } from './design/harness'
import { channels, people } from './design/fixtures'
// The signed founder/user identity made by Visual.fixture. The same identities
// give both renderers the same avatar colours; only storage is substituted.
const community = 'abb2d01c939f363dbe79b6767c412dcc0ca3857e9abb7917958b9ec7ac00816c'
const base = { community, communities: [community], communityNames: { [community]: 'Rowing club' }, ownUser: community,
  members: [{ ...people[0]!, user: community }], membership: { users: 1, devices: 1 }, channels: channels.slice(0, 1), channel: channels[0]!.id, unread: {}, messages: [], more: false, peers: 0, connectivity: { links: [], txBytes: 0, rxBytes: 0, ops: 4, dbBytes: 20_480, up: 0, down: 0 } }
const meta = { title: 'Parity/App', component: Window, parameters: { layout: 'fullscreen' } } satisfies Meta<typeof Window>
export default meta
type Story = StoryObj<typeof meta>
export const Home: Story = { args: harness({ ...base, viewing: 'list' }) }
export const Chat: Story = { args: harness({ ...base, viewing: 'channel' }) }
export const You: Story = { args: harness({ ...base, viewing: 'list', settings: { context: 'you', page: null } }) }
export const Appearance: Story = { args: harness({ ...base, ...turnedFrom('you'), viewing: 'list', settings: { context: 'you', page: 'appearance' } }) }
export const Community: Story = { args: harness({ ...base, viewing: 'channel', settings: { context: 'community', page: null } }) }
export const Channel: Story = { args: harness({ ...base, viewing: 'channel', settings: { context: 'channel', page: null } }) }
export const Retention: Story = { args: harness({ ...base, ...turnedFrom('community'), viewing: 'channel', settings: { context: 'community', page: 'retention' } }) }
export const Disappearing: Story = { args: harness({ ...base, ...turnedFrom('channel'), viewing: 'channel', settings: { context: 'channel', page: 'disappearing' } }) }
export const Storage: Story = { args: harness({ ...base, ...turnedFrom('community'), viewing: 'channel', settings: { context: 'community', page: 'storage' } }) }
export const Leave: Story = { args: harness({ ...base, ...turnedFrom('community'), viewing: 'channel', settings: { context: 'community', page: 'remove' } }) }
export const About: Story = { args: harness({ ...base, ...turnedFrom('you'), viewing: 'list', settings: { context: 'you', page: 'about' } }) }
// A node in no community: App.svelte's full-window "blank" screen (Get started),
// with no shell and so no sidebar.
export const GetStarted: Story = { args: harness({ ...base, community: null, communities: [], communityNames: {}, members: [], channels: [], channel: null }) }

const text = [
  'Boathouse code changed this morning. It is 4417 now.',
  'Same one for the side gate.', 'Ignore the laminated sign; nobody has replaced it.',
  'I will bring a spare key on Saturday.',
  'Forecast for Saturday is 14 knots gusting 22 from the south-west. I would rather take the pair out and do the long piece on Sunday when it drops to eight.',
  'Meet at the boathouse at seven.', 'See you there!',
]
export const Conversation: Story = { args: harness({ ...base, viewing: 'channel', messages: text.map((text, i) => ({
  opId: (i + 1).toString(16).padStart(64, '0'), author: people[0]!.device, authorUser: community,
  text, counter: String(i + 1), createdAt: (840 + i + (i >= 4 ? 6 : 0)) * 60_000,
})) }) }

// Deterministic signed identities emitted by Visual.sidebarPeople.
const sidebarMembers = [
  {
    "device": "abb2d01c939f363dbe79b6767c412dcc0ca3857e9abb7917958b9ec7ac00816c",
    "user": "abb2d01c939f363dbe79b6767c412dcc0ca3857e9abb7917958b9ec7ac00816c",
    "name": "Alice Nakamura",
    "kind": "person",
    "foundingDevice": false
  },
  {
    "device": "eb9085dfaec84f152c0be85f075c13ce02f24b46389b749811130958a2194057",
    "user": "eb9085dfaec84f152c0be85f075c13ce02f24b46389b749811130958a2194057",
    "name": "Alexandria Montgomery-Worcester",
    "kind": "person",
    "foundingDevice": false
  },
  {
    "device": "41ecc1eaa798208b6153220c725c530617456274028ed4cd0310c48c782e3fb3",
    "user": "41ecc1eaa798208b6153220c725c530617456274028ed4cd0310c48c782e3fb3",
    "name": "Анна",
    "kind": "person",
    "foundingDevice": false
  },
  {
    "device": "e19d70b70cd808fff6cff5d1e5b87c8400ecbe7b5f8cd39b8bde73ebfd781321",
    "user": "e19d70b70cd808fff6cff5d1e5b87c8400ecbe7b5f8cd39b8bde73ebfd781321",
    "name": "Zoë",
    "kind": "person",
    "foundingDevice": false
  },
  {
    "device": "08667d27101305a9a6dc534657353bbbb04300c16f9849eec89763dd3bc15c46",
    "user": "08667d27101305a9a6dc534657353bbbb04300c16f9849eec89763dd3bc15c46",
    "name": "Søren",
    "kind": "person",
    "foundingDevice": false
  },
  {
    "device": "cc1ee9e053ade2e760cf38200c572d0cae0bfc8360cfea4a8258b48b7784088b",
    "user": "cc1ee9e053ade2e760cf38200c572d0cae0bfc8360cfea4a8258b48b7784088b",
    "name": "Cassie Oyelaran",
    "kind": "person",
    "foundingDevice": false
  },
  {
    "device": "032485dd324f397f7aa096303f77ad72861b978b2056036b1374d4eab617dd1b",
    "user": "032485dd324f397f7aa096303f77ad72861b978b2056036b1374d4eab617dd1b",
    "name": "Γιώργος",
    "kind": "person",
    "foundingDevice": false
  },
  {
    "device": "2cb2ecc8eeec39adfe046cd8b8284cb82a5e4c0c5b08e18c340082fdd009c153",
    "user": "2cb2ecc8eeec39adfe046cd8b8284cb82a5e4c0c5b08e18c340082fdd009c153",
    "name": "Bo Andersen",
    "kind": "person",
    "foundingDevice": false
  }
] as const
export const Sidebar: Story = { args: harness({ ...base, viewing: 'channel', members: [...sidebarMembers] }) }

// Actual accepted identities emitted by Visual.switcherCommunities.
const switcherCommunities = [
  [
    "3669574cf1e123df1523c507c17c8b11d0e9061764d5b22873cc72405f63225e",
    "Alexandria's community with a long name"
  ],
  [
    "ade8d01cdb4aedb6be5e0ce49be3de29622d41bacd19a211d967b1536d7fd7cc",
    "Community 10"
  ],
  [
    "5f29de294fd87f3ab422ee305186d0799785b163cbc76820c10ca688e051479a",
    "Community 11"
  ],
  [
    "b6554823c07d9e365c40507cef9d534c8e1a4f78ab1e4b8e377be477a2607d80",
    "Community 12"
  ],
  [
    "485cb2331220d05404a24080b5053d46dc37ce873c1294006841fbf2a96c82b0",
    "Community 13"
  ],
  [
    "29ffe100c7ae7ddadfbc9489cd11c1aac95861019203e4bc1bc86a670fd5828e",
    "Community 14"
  ],
  [
    "abe39edfbc469756aadeb432bb564b82ecf0d53811cfcd0a5ef2ab0f369afab4",
    "Community 15"
  ],
  [
    "99b07455ad07c0fb6e673962d5843c377b1bf29a5f44ad86ab886f13196e0566",
    "Community 16"
  ],
  [
    "feaef25bd00d7b39147cb594c9bfd397bafb99012539edfab4600951c1a95508",
    "Community 3"
  ],
  [
    "844c272c9a604ff6b4bc4ec0d692e77368f56cdb2d299dcf3f8cd6c81bf95216",
    "Community 4"
  ],
  [
    "f9694fe01cccd578ece2796bc392d7b4c2320ca42fd65152e1af30b28347b825",
    "Community 5"
  ],
  [
    "652160637f42f0d2e111caffc3f61ed2e424317b3a5397af5c886875e2a5b55c",
    "Community 6"
  ],
  [
    "a6ea27b67fdff5e0381b0397a27b9d21f3f7f8f6c7ba5569fdfccbdfe93641a9",
    "Community 7"
  ],
  [
    "1416333e7e5c5d4589350bf1186d708e34e499994fe8ae6d2629c9e2b90a5f0b",
    "Community 8"
  ],
  [
    "2385c55dfbf1b734a24003b26c2c32e83333c7111cae5511b88ba612cc450092",
    "Community 9"
  ],
  [
    "abb2d01c939f363dbe79b6767c412dcc0ca3857e9abb7917958b9ec7ac00816c",
    "Rowing club"
  ],
  [
    "64844ab4c4a3d86c53722dd428457675aa392b8d982db10a333bca252aed2c4a",
    "Zoë & Søren"
  ]
] as const
const switching = { ...base, viewing: 'channel' as const, switching: true }
export const Switcher: Story = { args: harness(switching) }
export const SwitcherHover: Story = { args: harness(switching) }
const many = { ...switching, communities: switcherCommunities.map(([id]) => id), communityNames: Object.fromEntries(switcherCommunities) }
export const SwitcherMany: Story = { args: harness(many) }
export const SwitcherEnd: Story = { args: harness(many) }
