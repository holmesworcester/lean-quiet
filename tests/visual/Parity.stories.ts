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
