// encrypt.js

document.addEventListener('DOMContentLoaded', (event) => {
    document.body.addEventListener('click', function(e) {
        if (e.target && e.target.nodeName == "BUTTON" && e.target.getAttribute("data-action") === "validatePwd") {
            const pwdInput = e.target.previousElementSibling;
            const pwdContainer = e.target.closest('.pwd-container');
            const password = pwdInput.value;
            const correctPassword = pwdContainer.getAttribute('data-password');
            const contentToShow = pwdContainer.querySelector('.encrypted-content');

            if (password === correctPassword) {
                contentToShow.style.display = 'block'; // Show the content
                pwdContainer.querySelector('.pwd-prompt').style.display = 'none'; // Hide the prompt
            } else {
                alert("密码错误，请重新输入");
            }
        }
    });
});

/**
 * Docsify 插件钩子，用于在每次页面内容加载后处理加密标签。
 */
function afterEachHook(hook, vm) {
    hook.afterEach(function (html) {
        // Auto-generate IDs for each pwd block for easier management
        let uniqueIdCounter = 0;

        // Replace <pwd> tags with a custom HTML structure
        html = html.replace(/<pwd\s+value=['"](.*?)['"]>([\s\S]*?)<\/pwd>/g, function (_, password, content) {
            const id = `encrypted-${uniqueIdCounter++}`;
            return `
                <div class="pwd-container" id="${id}" data-password="${password}">
                    <div class="pwd-prompt" style="text-align: center;">
                        <input type="password" /><button data-action="validatePwd">查看内容</button>
                    </div>
                    <div class="encrypted-content" style="display: none;">${content}</div>
                </div>
            `;
        });

        return html;
    });
}

window.$docsify.plugins = [].concat(afterEachHook, window.$docsify.plugins || []);
