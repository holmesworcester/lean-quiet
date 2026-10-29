import type { Meta, StoryObj } from '@storybook/svelte-vite'
import Window from './design/Window.svelte'
import { harness } from './design/harness'
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
export const Appearance: Story = { args: harness({ ...base, viewing: 'list', settings: { context: 'you', page: 'appearance' } }) }
export const Community: Story = { args: harness({ ...base, viewing: 'channel', settings: { context: 'community', page: null } }) }
export const Channel: Story = { args: harness({ ...base, viewing: 'channel', settings: { context: 'channel', page: null } }) }
