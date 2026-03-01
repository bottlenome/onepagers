/* ═══════════════════════════════════════
   プラグインシステム (ソーシャル機能拡張用)
   ═══════════════════════════════════════ */
const PluginAPI = {
  plugins: [],
  register(plugin) {
    this.plugins.push(plugin);
    if (plugin.init) plugin.init();
    console.log(`[Plugin] ${plugin.name} registered`);
  },
  getExtraFacilities(townId) {
    return this.plugins.flatMap(p =>
      (p.facilities && p.facilities[townId]) || []
    );
  },
  renderScreen(screenId) {
    for (const p of this.plugins) {
      if (p.screens && p.screens[screenId]) return p.screens[screenId]();
    }
    return null;
  },
};

// --- 酒場プラグイン (スタブ) ---
// PluginAPI.register({
//   name: '酒場',
//   facilities: { castle: [{ id:'tavern', icon:'🍺', label:'酒場' }] },
//   screens: { tavern: () => '<h2>酒場</h2><p>チャット機能は今後実装予定です</p>' },
// });

// --- 対人闘技場プラグイン (スタブ) ---
// PluginAPI.register({
//   name: '対人闘技場',
//   facilities: { castle: [{ id:'pvp_arena', icon:'🏟️', label:'対人闘技場' }] },
//   screens: { pvp_arena: () => '<h2>対人闘技場</h2><p>PvP機能は今後実装予定です</p>' },
// });
