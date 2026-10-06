import fs from 'node:fs';
import path from 'node:path';
import crypto from 'node:crypto';
import { createRequire } from 'node:module';
import { fileURLToPath, pathToFileURL } from 'node:url';

const root = path.dirname(fileURLToPath(import.meta.url));
const dependencyRoot = process.argv[2] ? path.resolve(process.argv[2]) : root;
const requireDependency = createRequire(path.join(dependencyRoot, 'package.json'));
const { marked } = await import(pathToFileURL(requireDependency.resolve('marked')));
const temml = requireDependency('temml');
const source = fs.readFileSync(path.join(root, 'ftqclib.md'), 'utf8').replaceAll('\r\n', '\n');
const template = fs.readFileSync(path.join(root, 'STYLE-PUBLIC.html'), 'utf8');
const hash = text => crypto.createHash('sha256').update(text).digest('hex');
const escapeHtml = text => text.replaceAll('&', '&amp;').replaceAll('<', '&lt;').replaceAll('>', '&gt;').replaceAll('"', '&quot;');
const slug = text => text.toLowerCase().replace(/[^a-z0-9]+/g, '-').replace(/^-|-$/g, '');
const figures = new Map();
const title = source.match(/^# (.+)$/m)?.[1];
if (!title) throw new Error('The Markdown must begin with a title.');
const excerptRegistry = JSON.parse(fs.readFileSync(path.join(root, 'lean-excerpts.json'), 'utf8'));
const codeBlocks = [...source.matchAll(/```lean\n([\s\S]*?)\n```/g)].map(m => m[1]);
if (codeBlocks.length !== excerptRegistry.excerpts.length) throw new Error('Lean excerpt count differs from registry.');
for (const snippet of codeBlocks) {
  if (!excerptRegistry.excerpts.some(e => e.code === snippet)) throw new Error('A Lean excerpt differs from the inspected source.');
}

function math(tex, displayMode) {
  // STYLE-PUBLIC owns display-math layout; remove only Temml's equivalent root decoration.
  const result = temml.renderToString(tex, { displayMode, throwOnError: true, trust: false })
    .replace('<math display="block" class="tml-display" style="display:block math;">', '<math display="block">')
    // These Unicode mathematical-script letters already carry their semantic alphabet.
    .replace(/<mi class="mathcal">([𝒞𝒢])<\/mi>/gu, '<mi>$1</mi>');
  if (/\sstyle=/.test(result)) throw new Error(`Inline math style is forbidden: ${tex}`);
  for (const found of result.matchAll(/class="([^"]+)"/g)) {
    if (!/^tml-(sml|med|lrg)-pad$/.test(found[1])) throw new Error(`Unexpected math class: ${found[1]}`);
  }
  return result;
}

marked.use({
  renderer: {
    tablecell(token) {
      const tag = token.header ? 'th' : 'td';
      const scope = token.header ? ' scope="col"' : '';
      return `<${tag}${scope}>${this.parser.parseInline(token.tokens)}</${tag}>\n`;
    },
    heading(token) {
      const explicit = token.text.match(/\s+\{#([a-z0-9-]+)\}$/);
      const content = token.text.replace(/\s+\{#[a-z0-9-]+\}$/, '');
      const id = explicit?.[1] || slug(content);
      return `<h${token.depth} id="${id}">${marked.parseInline(content)}</h${token.depth}>\n`;
    }
  },
  extensions: [
    {
      name: 'displayMath', level: 'block', start: text => text.indexOf('$$'),
      tokenizer(text) {
        const match = text.match(/^\$\$\s*\n([\s\S]+?)\n\$\$(?:\n|$)/);
        if (match) return { type: 'displayMath', raw: match[0], tex: match[1] };
      }, renderer: token => `${math(token.tex, true)}\n`
    },
    {
      name: 'inlineMath', level: 'inline', start: text => text.indexOf('$'),
      tokenizer(text) {
        const match = text.match(/^\$([^$\n]+)\$/);
        if (match) return { type: 'inlineMath', raw: match[0], tex: match[1] };
      }, renderer: token => math(token.tex, false)
    },
    {
      name: 'semanticBlock', level: 'block', start: text => text.indexOf(':::'),
      tokenizer(text) {
        const match = text.match(/^:::(figure|proposition|theorem|proof|proof-sketch)(?: ([^\n]+))?\n([\s\S]*?)\n:::(?:\n|$)/);
        if (match) return {type:'semanticBlock',raw:match[0],kind:match[1],label:match[2]||'',body:match[3]};
      },
      renderer(token) {
        if (token.kind === 'figure') {
          if (!/^[a-z0-9-]+\.svg$/.test(token.label)) throw new Error('Invalid figure filename.');
          const svg = fs.readFileSync(path.join(root, 'figures', token.label), 'utf8').trim();
          if (!/<title>[^<]+<\/title>/.test(svg) || !/role="img"/.test(svg)) throw new Error('Figure needs title and role.');
          if (/<script|<style|<image|\son\w+=|(?:href|src)="https?:/i.test(svg)) throw new Error('Figure contains an unsupported dependency.');
          figures.set(token.label, hash(svg));
          const caption = token.body.match(/^\*\*(Figure \d+\.)\*\*\s*([\s\S]*)$/);
          if (!caption) throw new Error('Figure caption needs a numbered label.');
          return `<figure>\n${svg}\n<figcaption><b>${caption[1]}</b>${marked.parseInline(caption[2])}</figcaption>\n</figure>\n`;
        }
        const names = { proposition: 'Proposition', theorem: 'Theorem', proof: 'Proof', 'proof-sketch': 'Proof sketch' };
        const label = `${names[token.kind]}${token.label ? ` — ${token.label}` : ''}`;
        return `<section class="${token.kind}" aria-label="${escapeHtml(label)}">\n<p><strong>${escapeHtml(label)}.</strong></p>\n${marked.parse(token.body)}</section>\n`;
      }
    }
  ]
});

const body = marked.parse(source.replace(/^# .+\r?\n/, '').trim());
const templateHead = template.match(/<head>[\s\S]*?<\/head>/)?.[0];
if (!templateHead) throw new Error('Missing style template head.');
// Only document metadata changes; the complete style and its semantic rules are copied verbatim.
const head = templateHead.replace(/<title>[\s\S]*?<\/title>/, `<title>${escapeHtml(title)}</title>`);
const html = `<!doctype html>\n<html lang="en">\n${head}\n<body>\n<header>\n<p class="meta">ftqclib · overview</p>\n<h1>${escapeHtml(title)}</h1>\n<p class="meta">An introduction to the project's mathematics, formal methods, and purpose.</p>\n</header>\n<main>\n${body}</main>\n<footer>\n<p class="meta">Source snapshot: d66ec2b, as published at ftqclib.pages.dev. Prepared <time datetime="2026-10-05">5 October 2026</time>. Editable Markdown and SVG sources accompany this self-contained reading edition.</p>\n</footer>\n</body>\n</html>\n`;
const markup = html.replace(/<!--[\s\S]*?-->/g, '');
if (/<script\b|<link\b|<iframe\b|\sstyle=|\son\w+=/i.test(markup)) throw new Error('Output contains forbidden active or external content.');
const allIds = [...markup.matchAll(/\sid="([^"]+)"/g)].map(x=>x[1]);
if (allIds.length !== new Set(allIds).size) throw new Error('Duplicate document IDs.');
for (const link of markup.matchAll(/href="#([^"]+)"/g)) {
  if (!allIds.includes(link[1])) throw new Error(`Broken internal link: ${link[1]}`);
}
const style = head.match(/<style>[\s\S]*?<\/style>/)[0];
const templateStyle = templateHead.match(/<style>[\s\S]*?<\/style>/)[0];
if (style !== templateStyle) throw new Error('STYLE-PUBLIC stylesheet was changed.');
const destination = path.resolve(root, '..', 'index.html');
fs.writeFileSync(destination, html, 'utf8');
const manifest = {
  title, sourceSnapshot: 'd66ec2b (published embedded source)',
  plan: {targets:'08f4171e1623',steps:'78711b2a934e',inspected:'2026-10-05'},
  build: {marked:'17.0.5', temml:'0.13.5'},
  sha256: { markdown:hash(source), template:hash(template), stylesheet:hash(style), builder:hash(fs.readFileSync(fileURLToPath(import.meta.url))), leanRegistry:hash(fs.readFileSync(path.join(root,'lean-excerpts.json'))), html:hash(html), figures:Object.fromEntries(figures) },
  content: {figures:figures.size, leanBlocks:codeBlocks.length, mathElements:[...markup.matchAll(/<math\b/g)].length, mainWords:source.split('## Sources and scope')[0].replace(/```lean[\s\S]*?```/g,'').split(/\s+/).length},
  checks: {noActiveContent:true,internalLinksResolve:true,uniqueIds:true,stylesheetUnchanged:true,leanExcerptsMatchRegistry:true},
  note:'Document build and source review only; no independent Lean rebuild.'
};
fs.writeFileSync(path.resolve(root, '..', 'build-manifest.json'), JSON.stringify(manifest, null, 2)+'\n');
console.log(JSON.stringify({output:destination,...manifest.content}));
