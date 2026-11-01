// The live previews: which folder shows which, the browser kernel function
// it runs (if any), and the threat-model entries it touches.
export const previews = {
  app: {gap: 'One client over a fixture store. The native app runs the engine and SQLite.'},
  network: {gap: 'Two client stores and a delivery queue you control. Transport and signatures are simulated.'},
  message: {gap: 'Fixture data. The native row reads the message fact and its content key.'},
  'message.reaction': {target: 'validate', requirements: ['ICTM.D6', 'ICTM.A2', 'ICTM.A4', 'ICTM.H4'],
    gap: 'Workspace.validate stands in for the validator: fixture inputs, no signatures or codecs.'},
  'message.draft': {gap: 'Drafts are session overlays here. The draft op is planned.'},
  profile: {gap: 'A fixture profile.'},
  emoji: {gap: 'The built-in catalogue (assets/picker.txt). Custom emoji ops are planned.'},
  'settings.appearance': {target: 'theme', gap: 'The resolver runs in WASM. On main the preference is a side table (ThemeStore).'},
  sync: {gap: 'A simulated queue. Open network to pause and step delivery.'},
};
