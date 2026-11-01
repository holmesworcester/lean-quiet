// Preserve the rest of the checked module when editing one executable definition.
export function definitionRange(source, name) {
  if (!/^[a-zA-Z_][\w]*$/.test(name)) throw new Error('Invalid declaration name');
  const match = new RegExp(`^def ${name}\\b`, 'm').exec(source);
  if (!match) throw new Error(`Missing definition: ${name}`);
  const separator = source.indexOf('\n\n', match.index);
  const end = separator === -1 ? source.length : separator;
  return {start: match.index, end, text: source.slice(match.index, end)};
}
export function replaceDefinition(source, name, draft) {
  const {start,end} = definitionRange(source,name);
  return source.slice(0,start) + draft + source.slice(end);
}
