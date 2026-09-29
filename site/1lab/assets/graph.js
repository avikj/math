/* Module-neighbourhood view over 1Lab's links.json format. */
(async () => {
  const root = document.getElementById('graph');
  if (!root) return;
  const [links, entries] = await Promise.all([
    fetch('static/links.json').then(r => r.json()),
    fetch('static/search.json').then(r => r.json())
  ]);
  const modules = new Map(entries.filter(x => !x.idType && !x.idAnchor.includes('#')).map(x => [x.idIdent, x.idAnchor]));
  const imports = new Map(), users = new Map();
  for (const [from, to] of links) {
    if (!imports.has(from)) imports.set(from, new Set());
    if (!users.has(to)) users.set(to, new Set());
    imports.get(from).add(to);
    users.get(to).add(from);
  }
  const controls = document.createElement('div');
  controls.className = 'graph-controls';
  const input = document.createElement('input');
  input.setAttribute('list', 'graph-modules');
  input.setAttribute('aria-label', 'Module');
  input.placeholder = 'Choose a module';
  const list = document.createElement('datalist');
  list.id = 'graph-modules';
  for (const module of modules.keys()) {
    const option = document.createElement('option');
    option.value = module;
    list.append(option);
  }
  const button = document.createElement('button');
  button.textContent = 'Show links';
  controls.append(input, button, list);
  const layout = document.createElement('div');
  layout.className = 'graph-layout';
  root.append(controls, layout);
  const address = new URL(location.href);
  input.value = address.searchParams.get('module') || 'Kernel.RewriteCertificate';
  function render() {
    const chosen = input.value.trim();
    layout.replaceChildren();
    address.searchParams.set('module', chosen);
    history.replaceState(null, '', address);
    const column = (title, values) => {
      const outer = document.createElement('section');
      outer.className = 'graph-column';
      const heading = document.createElement('h2');
      heading.textContent = title;
      outer.append(heading);
      if (!values.length) {
        const empty = document.createElement('p');
        empty.className = 'graph-muted';
        empty.textContent = 'No indexed modules';
        outer.append(empty);
      } else {
        const ul = document.createElement('ul');
        for (const name of values) {
          const li = document.createElement('li');
          const a = document.createElement('a');
          a.href = modules.get(name) || '#';
          a.textContent = name;
          li.append(a);
          ul.append(li);
        }
        outer.append(ul);
      }
      return outer;
    };
    const before = [...(users.get(chosen) || [])].sort();
    const after = [...(imports.get(chosen) || [])].sort();
    const centre = column('Selected module', []);
    const node = document.createElement('div');
    node.className = 'graph-node';
    if (modules.has(chosen)) {
      const a = document.createElement('a');
      a.href = modules.get(chosen);
      a.textContent = chosen;
      node.append(a);
    } else {
      node.textContent = 'Choose a module from the suggestions.';
    }
    centre.append(node);
    layout.append(column(`Imported by (${before.length})`, before), centre, column(`Imports (${after.length})`, after));
  }
  button.addEventListener('click', render);
  input.addEventListener('keydown', e => { if (e.key === 'Enter') render(); });
  render();
})();
