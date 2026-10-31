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
    "device": "3377061a86f826bb4bc7665bd8406e3e503a2f1070131076caaa9fbdbbd51cf1",
    "user": "3377061a86f826bb4bc7665bd8406e3e503a2f1070131076caaa9fbdbbd51cf1",
    "name": "Γιώργος",
    "kind": "person",
    "foundingDevice": false
  },
  {
    "device": "4b2e561ae545b30ffd2ae25d8883fd2e057bd602d7b01746f191a09d41d3cc7e",
    "user": "4b2e561ae545b30ffd2ae25d8883fd2e057bd602d7b01746f191a09d41d3cc7e",
    "name": "Zoë",
    "kind": "person",
    "foundingDevice": false
  },
  {
    "device": "08b5ff454b9312853ac56398888c09830eb1ddf9a97158edceb4ab1ef95bec55",
    "user": "08b5ff454b9312853ac56398888c09830eb1ddf9a97158edceb4ab1ef95bec55",
    "name": "Анна",
    "kind": "person",
    "foundingDevice": false
  },
  {
    "device": "1810fc0823eb98903ff73229f5ac979394b6cd93a7ff33bde436237a47f03d76",
    "user": "1810fc0823eb98903ff73229f5ac979394b6cd93a7ff33bde436237a47f03d76",
    "name": "Bo Andersen",
    "kind": "person",
    "foundingDevice": false
  },
  {
    "device": "75b417858d4eb3f82ee43e1518ccababcaa00617c73b4e605a7f528759df8d43",
    "user": "75b417858d4eb3f82ee43e1518ccababcaa00617c73b4e605a7f528759df8d43",
    "name": "Alexandria Montgomery-Worcester",
    "kind": "person",
    "foundingDevice": false
  },
  {
    "device": "c75c782b142a82523af57356c4d3323c78ad26a7e676a724f72f419964e42e5e",
    "user": "c75c782b142a82523af57356c4d3323c78ad26a7e676a724f72f419964e42e5e",
    "name": "Søren",
    "kind": "person",
    "foundingDevice": false
  },
  {
    "device": "8e1510e913caf3de59e9d574ad8f5b0116c5a7bc127d1e9da2c96824fa0b8019",
    "user": "8e1510e913caf3de59e9d574ad8f5b0116c5a7bc127d1e9da2c96824fa0b8019",
    "name": "Cassie Oyelaran",
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
