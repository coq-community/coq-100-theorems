#!/usr/bin/env node

// Requires:
// - node
// - npm package js-yaml
//
// Usage: ./gen.js > index.html

const yaml = require('js-yaml');
const fs = require('fs');

const read_yaml = filename => {
  try {
    return yaml.load(fs.readFileSync(filename, 'utf8'));
  } catch(e) {
    console.error(`Yaml parse error for file ${filename}: ${e.message}`);
    process.exit(1);
  }
}

// import theorems, statements, existing proofs
let theorems_names = read_yaml('theorems.yml');
let statements_list = read_yaml('statements.yml');
let existing_proofs = read_yaml('existing_proofs.yml');

// group statements by theorem
let theorems = [{}]
for(let id in theorems_names) {
  theorems[id] = { name : theorems_names[id], statements: [] };
}
for(let statement of statements_list) {
  let id = Number(statement.theorem);
  theorems[id].statements.push(statement)
}

// add maintainability information in link description
function link_description(url) {
  let m;
  if(m = url.match(/^https:\/\/github.com\/coq-community\/([^\/]*)\//))
    return `coq-community/${m[1]}`;
  if(m = url.match(/^https:\/\/github.com\/coq-contribs\/([^\/]*)\//))
    return `coq-contribs/${m[1]}`;
  let known_urls = [
    ["coq's standard library", "https://coq.inria.fr/library"],
    ["mathcomp", "https://math-comp.github.io/"],
    ["mathcomp", "https://github.com/math-comp/"],
    ["coq-contribs", "https://github.com/coq-contribs"],
    ["cocorico", "https://coq.inria.fr/cocorico/"],
    ["github repo (no known continous integration)", "https://github.com/"],
  ];
  for (let p of known_urls) {
    if (url.match(p[1])) return p[0];
  }
  return `${url} (no CI?)`;
}

const escapeHtml = str =>
  [[/&/g, "&amp;"], [/</g, "&lt;"], [/>/g, "&gt;"], [/"/g, "&quot;"], [/'/g, "&#039;"]]
  .reduce((s, [re, esc]) => s.replace(re, esc), str)

// generate HTML
let html = ""

for(let id = 1; id <= 100; id++) {
  let {name, statements} = theorems[id];
  let class_ = statements.length ? 'formalized' : 'notformalizedyet';
  html += `\n`;
  html += `<h3 id='${id}' class='${class_}'><a href='http://www.cs.ru.nl/~freek/100/#${id}'>${id}. ${name}</a></h3>\n`;
  html += `<div>\n`;
  for(let s of statements) {
    let {authors, link, comment, statement} = s;
    html += `
<strong class='author'>${escapeHtml(authors)}</strong>
  (in <a href="${link}">${s.link_description || link_description(link)}</a>):
<pre class='comment'>${comment || ''}</pre>
<pre class='statement'>${escapeHtml(statement)}</pre>
`
  }
  let existing = existing_proofs[id].join(', ') || '(none)';
  html += `<p class='existing'>Formalized in: ${existing}</p>`;
  html += `</div>\n`;
}

let nb_formalized_in_coq = theorems.filter(x => x.statements?.length).length;

// fill template with content
let page = fs.readFileSync('template.html', 'utf8')
  .replace('{{{main}}}', html)
  .replace('{{{nb_formalized_in_coq}}}', nb_formalized_in_coq)
;

process.stdout.write(page);
