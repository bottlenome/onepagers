// ===== メインロジック =====

// タブ切り替え
function switchTab(tabId) {
  document.querySelectorAll('.tab-content').forEach(el => el.classList.remove('active'));
  document.querySelectorAll('.tab-btn').forEach(el => el.classList.remove('active'));
  document.getElementById(tabId).classList.add('active');
  document.querySelector('[data-tab="' + tabId + '"]').classList.add('active');
}

// 初期化
document.addEventListener('DOMContentLoaded', () => {
  switchTab('tab-overview');
});
