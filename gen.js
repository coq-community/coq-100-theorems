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
  ];
  for (let p of known_urls) {
    if (url.match(p[1])) return p[0];
  }
  return `${url}`;
}

const escapeHtml = str =>
  [[/&/g, "&amp;"], [/</g, "&lt;"], [/>/g, "&gt;"], [/"/g, "&quot;"], [/'/g, "&#039;"]]
  .reduce((s, [re, esc]) => s.replace(re, esc), str)

// generate HTML
let html = "";

for(let id = 1; id <= 100; id++) {
  let {name, statements} = theorems[id];
  let class_ = statements.length ? 'formalized' : 'notformalizedyet';
  html += `\n`;
  html += `<h3 id='${id}' class='${class_}'><a href='http://www.cs.ru.nl/~freek/100/#${id}'>${id}. ${name}</a></h3>\n`;
  html += `<div>\n`;
  for(let s of statements) {
    let {authors, link, comment, statement} = s;
    html += `
<p class='author'><strong>${escapeHtml(authors)}</strong>
  (in <a href="${link}">${s.link_description || link_description(link)}</a>):
</p>
<p class='comment'>${comment || ''}</p>
<pre class='statement'>${escapeHtml(statement)}</pre>
`
    ;
    if("reproducibility" in s) {
      html += `<p class='repro'>Reproducibility: ${s.reproducibility}</p>\n`
    }
    if("constructive" in s) {
      html += `<p class='axioms'>Constructive: ${s.constructive}</p>\n`
    }
    if("axioms" in s) {
      if (s.axioms.length == 0) {
        html += `<p class='axioms'>Axioms used: (none)</p>\n`
      } else {
        html += `<p class='axioms'>Axioms used:</p>\n<ul class='axioms'>\n`
        for (let axiom of s.axioms) {
          html += `<li>${axiom}</li>\n`
        }
        html += `</ul>\n`
      }
    }
  }
  let existing = existing_proofs[id].join(', ') || '(none)';
  html += `<p class='existing'>Formalized in: ${existing}</p>`;
  html += `</div>\n`;
}

// display some infos
function count_values(l) {
  let c = {};
  for(let v of l) {
    c[v] = (c[v] || 0) + 1;
  }
  return c;
}

let constructive_at_freeks = Object.entries(existing_proofs).filter(([_, l]) => l.includes("Coq (constructive)")).map(([id, _]) => Number(id));
let constructive_here = Object.entries(theorems).filter(([_, s]) => s?.statements?.filter(s => s.constructive == 'yes').length > 0).map(([id, _]) => Number(id));
const array_difference = (s1, s2) => [...s1].filter(x => !s2.includes(x))

let stats = {
  formalized_in_coq: theorems.filter(t => t?.statements?.length).length,
  nb_statements: statements_list.length,
  nb_reproducibility_info: statements_list.filter(s => s.reproducibility).length,
  nb_axioms_info: statements_list.filter(s => s.axioms).length,
  nb_constructive_info: statements_list.filter(s => s.constructive).length,
  constructivity_values: count_values(statements_list.map(s => s.constructive)),
  missing_info: statements_list.filter(s => !s.axioms || !s.constructive || !s.reproducibility).map(s=>s.theorem + ' ' + s.link),
  constructive_only_here: array_difference(constructive_here, constructive_at_freeks),
  constructive_only_at_freeks:  array_difference(constructive_at_freeks, constructive_here),
}

console.warn(stats)

// fill template with content
let page = fs.readFileSync('template.html', 'utf8')
  .replace('{{{main}}}', html)
  .replace('{{{nb_formalized_in_coq}}}', stats.formalized_in_coq)
  .replace(/(?<=var stats = ){}/, JSON.stringify(stats, null, 2).replace(/\n/g, '\n      '))
;

process.stdout.write(page);
