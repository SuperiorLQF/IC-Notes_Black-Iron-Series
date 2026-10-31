// Import UI shared by the hosted editor and the self-contained preview.
function openImportDialog() {
    const list = document.getElementById('exampleList');
    list.replaceChildren();
    for (const example of window.DIGIWAVE_EXAMPLES || []) {
        const card = document.createElement('article');card.className = 'example-card';
        const title = document.createElement('h3');title.textContent = example.title;
        const description = document.createElement('p');description.textContent = example.description;
        const actions = document.createElement('div');actions.className = 'example-actions';
        const load = document.createElement('button');load.type = 'button';load.className = 'primary example-load';load.dataset.exampleId = example.id;load.textContent = 'Load';load.setAttribute('aria-label', 'Load ' + example.title);
        load.addEventListener('click', () => loadProtocolExample(example.id));
        const download = document.createElement('button');download.type = 'button';download.className = 'example-download';download.textContent = 'JSON ↓';download.setAttribute('aria-label', 'Download ' + example.title);
        download.addEventListener('click', () => downloadProtocolExample(example.id));
        actions.append(load,download);card.append(title,description,actions);list.append(card);
    }
    document.getElementById('importError').textContent = '';
    document.getElementById('importModal').style.display = 'flex';
    document.getElementById('importFileButton').focus();
}
function loadProtocolExample(id) {
    const example = (window.DIGIWAVE_EXAMPLES || []).find(item => item.id === id);
    if (!example) return;
    try {
        const data = validateProject(example.project);
        if (projectIsDirty() && !confirm(`加载 ${example.title} 将替换当前工程。请确认重要修改已导出；加载后可撤销。`)) return;
        applyProject(data);
        updateUI();fitWaveform();
        writeBackup();
    } catch (error) {
        document.getElementById('importError').textContent = '示例加载失败：' + error.message;
    }
}
function downloadProtocolExample(id) {
    const example = (window.DIGIWAVE_EXAMPLES || []).find(item => item.id === id);
    if (!example) return;
    const data = {...example.project, example: {title:example.title, description:example.description}};
    const url = URL.createObjectURL(new Blob([JSON.stringify(data,null,2)],{type:'application/json'}));
    const link=document.createElement('a');link.href=url;link.download=`digiwave-${id}.json`;link.click();URL.revokeObjectURL(url);
}
