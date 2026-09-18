import { test, expect } from '@playwright/test';
import { existsSync } from 'node:fs';
import { fileURLToPath } from 'node:url';

const pageURL = new URL('../index.html', import.meta.url).href;

test.beforeEach(async ({ page }) => {
  page.on('pageerror', error => { throw error; });
  await page.goto(pageURL);
});

test('offline pipeline filters, shared ownership, and evidence dialogs', async ({ page }) => {
  await expect(page.getByRole('heading', { name: 'From refresh to ready.' })).toBeVisible();
  await expect(page.locator('#work-count')).toContainText('26 of 26');
  await page.getByLabel('Find work').fill('W14');
  await expect(page.locator('#work-count')).toContainText('1 of 26');
  await expect(page.locator('[data-work="W14"]')).toHaveCount(2);
  await page.locator('[data-work="W14"]').first().click();
  await expect(page.getByRole('dialog')).toContainText('DURATION UNKNOWN');
  await page.getByRole('button', { name: 'K1', exact: true }).click();
  await expect(page.getByRole('dialog')).toContainText('KotlinCompilerArgumentsProducer.kt');
  await page.keyboard.press('Escape');
  await expect(page.getByRole('dialog')).not.toBeVisible();
  await page.getByLabel('Find work').fill('not-a-work-item');
  await expect(page.locator('#swimlane')).toContainText('No work items match');
  await page.getByLabel('Find work').fill('');
  await page.getByLabel('Owner', { exact: true }).selectOption('compiler-optional');
  await expect(page.locator('#work-count')).toContainText('1 of 26');
});

test('trace filters, pagination, attributes, repeated requests, and trace switching', async ({ page }) => {
  await page.getByRole('link', { name: '02 Trace explorer' }).click();
  await expect(page.locator('#span-count')).toContainText('969 of 969');
  await expect(page.locator('#trace-stats')).toContainText('38.660 s');
  await page.getByRole('button', { name: 'Next 100' }).click();
  await expect(page.locator('#span-count')).toContainText('101–200');
  await page.getByLabel('Find spans').fill('GradleSourceSetDependencyModelProvider');
  await expect(page.locator('#span-count')).toContainText('1 of 969');
  await page.locator('.span-row').click();
  await expect(page.getByRole('dialog')).toContainText('11.851 s');
  await expect(page.getByRole('dialog')).toContainText('Not CPU / self time');
  await page.getByRole('button', { name: 'Close details' }).click();
  await page.getByLabel('Find spans').fill('');
  await page.getByLabel('Error-tagged only').check();
  await expect(page.locator('#span-count')).toContainText('14 of 969');
  await page.getByLabel('Error-tagged only').uncheck();
  await expect(page.locator('.request-group')).toHaveCount(22);
  await page.locator('.request-group summary').first().click();
  await page.locator('.request-group [data-span]').first().click();
  await expect(page.getByRole('dialog')).toContainText('HEAD');
  await page.keyboard.press('Escape');
  await page.locator('#trace-select').selectOption({ index: 1 });
  await expect(page.locator('#span-count')).toContainText('2 of 2');
  await expect(page.locator('#repeats')).toContainText('No repeated');
});

test('benchmarks retain missing runs and explicitly separate warm-ups', async ({ page }) => {
  await page.getByRole('link', { name: '03 Benchmarks' }).click();
  await expect(page.locator('#bench-chart')).toContainText('154.418 s');
  await expect(page.locator('#bench-chart')).toContainText('104.147 s');
  await page.locator('#bench-scenario').selectOption('idea-sync-warm-warm-warm');
  await expect(page.locator('#bench-chart')).toContainText('2.046 s');
  await expect(page.locator('#bench-chart')).toContainText('Scenario not recorded');
  await expect(page.locator('#bench-iterations')).not.toContainText('WARM_UP');
  await page.getByLabel('Include warm-ups in statistics').check();
  await expect(page.locator('#bench-iterations')).toContainText('WARM_UP');
  await expect(page.locator('#bench-heading')).toContainText('includes warm-ups');
  const dependency = await page.locator('#bench-scenario option').evaluateAll(options => options.find(option => /Add Gson to core/i.test(option.textContent)).value);
  await page.locator('#bench-scenario').selectOption(dependency);
  await expect(page.locator('#bench-chart')).toContainText('Failed before samples');
  await expect(page.locator('#bench-chart .benchmark-bar')).toHaveCount(0);
});

test('all documentation renders, internal links navigate, and search finds full text', async ({ page }) => {
  await page.getByRole('link', { name: '05 Documentation' }).click();
  await expect(page.locator('#doc-results .doc-link')).toHaveCount(13);
  await page.getByLabel('Search all documentation').fill('fingerprint');
  await expect(page.locator('#doc-results .doc-link')).not.toHaveCount(13);
  await expect(page.locator('#doc-results')).toContainText('fingerprint');
  const docs = await page.evaluate(() => window.IMPORT_OVERVIEW.documents.map(doc => ({ path: doc.path, title: doc.title })));
  for (const doc of docs) {
    await page.goto(`${pageURL}#docs/${encodeURIComponent(doc.path)}`);
    await expect(page.locator('#document h1')).toHaveText(doc.title);
    await expect(page.locator('#document script')).toHaveCount(0);
    const links = await page.locator('#document a[href]').evaluateAll(links => links.map(link => link.href));
    for (const href of links.filter(href => href.startsWith('file:'))) {
      const url = new URL(href);
      if (url.hash.startsWith('#docs/')) {
        expect(docs.some(doc => doc.path === decodeURIComponent(url.hash.split('/')[1])), href).toBe(true);
      } else {
        expect(existsSync(fileURLToPath(url)), href).toBe(true);
      }
    }
  }
  await page.goto(`${pageURL}#docs/index.md`);
  await page.locator('#document').getByRole('link', { name: 'work inventory', exact: true }).click();
  await expect(page.locator('#document h1')).toHaveText('Work inventory by owner and demand');
  await page.goBack();
  await expect(page.locator('#document h1')).toHaveText('Kotlin/JVM Gradle import: work and swimlanes');
});

test('evidence search exposes source excerpts and every original file', async ({ page }) => {
  await page.getByRole('link', { name: '06 Evidence archive' }).click();
  await page.getByLabel('Find evidence').fill('Argument contribution categories');
  await expect(page.locator('.source-card')).toHaveCount(1);
  await page.locator('.source-card').click();
  await expect(page.getByRole('dialog')).toContainText('File SHA-256');
  await page.keyboard.press('Escape');
  await page.getByLabel('Find evidence').fill('');
  await page.getByLabel('Show', { exact: true }).selectOption('files');
  await expect(page.locator('#evidence-count')).toContainText('49 files');
  await page.getByLabel('Find evidence').fill('traces-1789726526259.json');
  await expect(page.locator('#evidence-results tbody tr')).toHaveCount(1);
  await expect(page.locator('#evidence-results a')).toHaveAttribute('href', '../import-overview/bin/traces/yahor/traces-1789726526259.json');
});

test('mobile navigation and each view stay inside the viewport', async ({ page }) => {
  await page.setViewportSize({ width: 390, height: 844 });
  for (const view of ['pipeline', 'trace', 'benchmarks', 'investigation', 'docs', 'evidence']) {
    await page.goto(`${pageURL}#${view}`);
    await expect(page.locator('main h1').first()).toBeVisible();
    const width = await page.evaluate(() => ({ body: document.documentElement.scrollWidth, viewport: innerWidth }));
    expect(width.body, view).toBeLessThanOrEqual(width.viewport);
  }
  await page.goto(`${pageURL}#pipeline`);
  await page.screenshot({ path: 'test-results/mobile-pipeline.png', fullPage: true });
});

test('page makes no external network requests and loads with offline browser', async ({ page, context }) => {
  const requests = [];
  page.on('request', request => { if (/^https?:/.test(request.url())) requests.push(request.url()); });
  await context.setOffline(true);
  await page.goto(`${pageURL}#pipeline`);
  await expect(page.locator('.work-card').first()).toBeVisible();
  await page.screenshot({ path: 'test-results/desktop-pipeline.png', fullPage: true });
  expect(requests).toEqual([]);
});

test('investigation summaries are derived from evidence and retain caveats', async ({ page }) => {
  await page.getByRole('link', { name: '04 Investigation' }).click();
  await expect(page.locator('.stat strong')).toHaveText(['22', '0.460 s', '10']);
  await expect(page.locator('.prose')).toContainText('No candidate optimization was implemented');
  await expect(page.locator('.prose')).toContainText('nondefault');
});

test('Markdown strips executable HTML without losing readable content', async ({ page }) => {
  await page.evaluate(() => {
    window.IMPORT_OVERVIEW.documents.push({
      path: 'test.md', title: 'Safety fixture',
      markdown: '# Safety fixture\n<script>window.compromised = true</script>\n<img src="missing" onerror="window.compromised = true">\n[unsafe](javascript:alert(1))\n**Readable content**',
    });
    location.hash = '#docs/test.md';
  });
  await expect(page.locator('#document')).toContainText('Readable content');
  await expect(page.locator('#document script, #document [onerror], #document [href^="javascript:"]')).toHaveCount(0);
  expect(await page.evaluate(() => window.compromised)).toBeUndefined();
});