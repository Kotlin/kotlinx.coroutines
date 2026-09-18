import { build } from 'esbuild';
import { execFileSync } from 'node:child_process';
import { readFileSync, writeFileSync } from 'node:fs';
import { fileURLToPath } from 'node:url';

process.chdir(fileURLToPath(new URL('.', import.meta.url)));
execFileSync('python3', ['build_data.py'], { stdio: 'inherit' });
await build({
  entryPoints: ['src/app.js'],
  bundle: true,
  minify: true,
  outfile: 'app.js',
  legalComments: 'eof',
});
const notices = ['Bundled third-party libraries. Sources are unmodified, then bundled/minified.\n'];
for (const name of ['marked', 'dompurify']) {
  const pkg = JSON.parse(readFileSync(`node_modules/${name}/package.json`, 'utf8'));
  notices.push(`${name} ${pkg.version}\n${pkg.homepage}\n\n${readFileSync(`node_modules/${name}/LICENSE`, 'utf8')}`);
}
writeFileSync('THIRD_PARTY_LICENSES.txt', notices.join('\n\n---\n\n'));