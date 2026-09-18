import { defineConfig } from '@playwright/test';

export default defineConfig({
  testDir: './tests',
  testMatch: '**/*.spec.js',
  fullyParallel: true,
  use: { browserName: 'chromium', viewport: { width: 1440, height: 1000 } },
});