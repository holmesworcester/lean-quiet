import { defineConfig } from "@playwright/test";
export default defineConfig({
  testDir: "./tests/browser",
  timeout: 30000,
  fullyParallel: false,
  workers: 1,
  reporter: "list",
  outputDir: "test-results",
  use: {
    baseURL: `http://127.0.0.1:${process.env.WORKSPACE_PORT || 4173}`,
    screenshot: "only-on-failure",
    trace: "retain-on-failure",
    launchOptions: process.env.PLAYWRIGHT_CHROMIUM_EXECUTABLE
      ? { executablePath: process.env.PLAYWRIGHT_CHROMIUM_EXECUTABLE }
      : {},
  },
  webServer: {
    command: `python3 tools/serve.py --port ${process.env.WORKSPACE_PORT || 4173}`,
    url: `http://127.0.0.1:${process.env.WORKSPACE_PORT || 4173}`,
    reuseExistingServer: !process.env.CI,
    timeout: 10000,
  },
});
