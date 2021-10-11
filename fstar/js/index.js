var runtime = {
  caml_thread_initialize: () => {}
};

window.addEventListener("load", () => {
  let pre = document.querySelector("pre");
  pre.appendChild(document.createTextNode("Page loaded"));
  debug();
});
