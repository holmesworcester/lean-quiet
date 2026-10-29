import type { Meta, StoryObj } from '@storybook/svelte-vite'
import Window from './design/Window.svelte'
import { harness, turnedFrom } from './design/harness'
import { channels, people } from './design/fixtures'
// The signed founder/user identity made by Visual.fixture. The same identities
// give both renderers the same avatar colours; only storage is substituted.
const community = 'c40af42a697cdcf30451f2d97ab8d6046d91fcc8c74830392fb433da90ee0a07'
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
    "device": "c40af42a697cdcf30451f2d97ab8d6046d91fcc8c74830392fb433da90ee0a07",
    "user": "c40af42a697cdcf30451f2d97ab8d6046d91fcc8c74830392fb433da90ee0a07",
    "name": "Alice Nakamura",
    "kind": "person",
    "foundingDevice": false
  },
  {
    "device": "34fd20934f8c8de8a492af3ddec936408b0c49539f676a7fa7e78f26cd56098f",
    "user": "34fd20934f8c8de8a492af3ddec936408b0c49539f676a7fa7e78f26cd56098f",
    "name": "Bo Andersen",
    "kind": "person",
    "foundingDevice": false
  },
  {
    "device": "7d3671c14c48c7360c1dd625d027e974a77423bb25c72051beb76f24011cfc41",
    "user": "7d3671c14c48c7360c1dd625d027e974a77423bb25c72051beb76f24011cfc41",
    "name": "Zoë",
    "kind": "person",
    "foundingDevice": false
  },
  {
    "device": "cd3d5fdc3d078a92de972fb6adbce45ef603695a15526ed342d5d39af6507571",
    "user": "cd3d5fdc3d078a92de972fb6adbce45ef603695a15526ed342d5d39af6507571",
    "name": "Søren",
    "kind": "person",
    "foundingDevice": false
  },
  {
    "device": "c5f610f6a0df5152c452b68547e4f0f9ce653ad70aec9e0e246f3c877cb0e7bf",
    "user": "c5f610f6a0df5152c452b68547e4f0f9ce653ad70aec9e0e246f3c877cb0e7bf",
    "name": "Cassie Oyelaran",
    "kind": "person",
    "foundingDevice": false
  },
  {
    "device": "41c6c77725aa52f153286e4b8f390b27682c0de410616b6ce12c950ba545a5a4",
    "user": "41c6c77725aa52f153286e4b8f390b27682c0de410616b6ce12c950ba545a5a4",
    "name": "Γιώργος",
    "kind": "person",
    "foundingDevice": false
  },
  {
    "device": "57d3e93fe35d7ab59237b299194844872e284b359ff9e5cf087c8153a203582d",
    "user": "57d3e93fe35d7ab59237b299194844872e284b359ff9e5cf087c8153a203582d",
    "name": "Анна",
    "kind": "person",
    "foundingDevice": false
  },
  {
    "device": "072c431429f968965b9f447f0919b3c52e334bcacd53ea683ecacf4df06ec25c",
    "user": "072c431429f968965b9f447f0919b3c52e334bcacd53ea683ecacf4df06ec25c",
    "name": "Alexandria Montgomery-Worcester",
    "kind": "person",
    "foundingDevice": false
  }
] as const
export const Sidebar: Story = { args: harness({ ...base, viewing: 'channel', members: [...sidebarMembers] }) }

// Actual accepted identities emitted by Visual.switcherCommunities.
const switcherCommunities = [
  [
    "4ff2db540dfb34156b87d992c15639bd65734d8fd86be0a808c41cebff25aa52",
    "Alexandria's community with a long name"
  ],
  [
    "953ab69261ec0785bd2df28a122be1b391170cf4d5698ffb60a173c53f0c694e",
    "Community 10"
  ],
  [
    "043e2295d06b71722d1f50001eb1932501c86fa1c62eee1c6caa68f887993a38",
    "Community 11"
  ],
  [
    "849b36bbfdb2728194f01943413edf9af2768df5822bc32152ff2526e2127cd7",
    "Community 12"
  ],
  [
    "2b0ba90aa6cb19ee29d82b36d25dbe5c428e8776b7beeb8388b5124d09587ad5",
    "Community 13"
  ],
  [
    "ef43cdfda9f20320961f67bc3b0a21372ddb43229b47e7e331b5c799d49c49ab",
    "Community 14"
  ],
  [
    "361dbe6f7fcbed85a3e3c352b0bbf1d552afd039582519431055a41caa1f6f97",
    "Community 15"
  ],
  [
    "1767134701873d8b435f1ad30f85d1a23ea56c2753776ab709b9c5a02c413bce",
    "Community 16"
  ],
  [
    "ff98d3c5d56d11853b2f7ac858e6895aba655a68e522bf299423af55b37786e4",
    "Community 3"
  ],
  [
    "b2320ed52da8c217624ec7da8cfa4b9c22d9fdee76a16f8904499d94b48a6add",
    "Community 4"
  ],
  [
    "380c80cc1b314d6555394e53d5863474cdf11718648ec53be799ef475f01fa21",
    "Community 5"
  ],
  [
    "959c6b8de2bf45c1ae7564ca8c9dd66c68f2720366fe313ad376b018b61cf7b7",
    "Community 6"
  ],
  [
    "469cd07f3a866a94f56938e9ef3f1a5a9dac43bac0296296031f0bad100e3a6a",
    "Community 7"
  ],
  [
    "f60514cde5f6fa119f78865ee939c27906b9eeb1087a190b6a2c3432c4ee8a8b",
    "Community 8"
  ],
  [
    "2bf3dabe436f1817739b4ab3c3dc613f2d79aafe65e13328af8ce7398bbc8a24",
    "Community 9"
  ],
  [
    "c40af42a697cdcf30451f2d97ab8d6046d91fcc8c74830392fb433da90ee0a07",
    "Rowing club"
  ],
  [
    "5ccd09cacb7a5d2f5987def416b8755f8020f6d1d2382f5bcca5cda365060071",
    "Zoë & Søren"
  ]
] as const
const switching = { ...base, viewing: 'channel' as const, switching: true }
export const Switcher: Story = { args: harness(switching) }
export const SwitcherHover: Story = { args: harness(switching) }
const many = { ...switching, communities: switcherCommunities.map(([id]) => id), communityNames: Object.fromEntries(switcherCommunities) }
export const SwitcherMany: Story = { args: harness(many) }
export const SwitcherEnd: Story = { args: harness(many) }
