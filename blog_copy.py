# -*- coding: utf-8 -*-
"""
Created on Wed Dec 31 11:00:59 2025

@author: MikeXu

部落格備份程式
"""
import os
import sys
import json
import time
import requests
from bs4 import BeautifulSoup
from urllib.parse import urljoin, urlparse, unquote
import re
from requests.adapters import HTTPAdapter
from urllib3.util.retry import Retry
import urllib3  # 新增：用於在關閉 SSL 驗證時抑制警告訊息


# === 動態路徑定位：確保程式不論「直接執行 .py」或「打包成 .exe」都能正確找到同資料夾底下的檔案 ===
if getattr(sys, "frozen", False):
    # 如果程式被 PyInstaller 等工具打包成 .exe，取得該 .exe 所在的資料夾路徑
    _APP_DIR = os.path.dirname(sys.executable)
else:
    # 如果是直接執行 .py 原始碼，取得該 .py 檔案所在的資料夾路徑
    _APP_DIR = os.path.dirname(os.path.abspath(__file__))


# ============================================================
#  可調整設定區（要改參數，改這裡就好，不用翻下面的程式）
# ============================================================

# --- 檔案與資料夾 ---
MEMBERS_FILENAME = "members.json"        # 成員對照表檔名
BACKUP_ROOT      = "Sakurazaka_Backup"   # 備份輸出的主資料夾名稱
ARTICLE_SUBDIR   = "details"             # 文章內頁存放的子資料夾名稱

# --- 目標網站 ---
BASE_LIST_URL = "https://sakurazaka46.com/s/s46/diary/blog/list"  # 部落格列表頁網址

# --- 連線行為 ---
REQUEST_TIMEOUT = 30    # 每次連線的逾時秒數（怕網路 lag 可調大）
PAGE_DELAY      = 1     # 每掃描完一頁列表後的等待秒數（放慢速度、對伺服器友善）
USER_AGENT      = ("Mozilla/5.0 (Windows NT 10.0; Win64; x64) "
                   "AppleWebKit/537.36 (KHTML, like Gecko) "
                   "Chrome/120.0.0.0 Safari/537.36")

# --- 失敗自動重試 ---
MAX_RETRIES        = 3                    # 連線失敗最多重試次數
RETRY_BACKOFF      = 1                    # 重試間隔倍率（1 → 約 1秒, 2秒, 4秒...）
RETRY_STATUS_CODES = [500, 502, 503, 504] # 遇到這些 HTTP 狀態碼才重試

# --- 頁面結構相關（若官網改版導致抓取失效，來這裡對照新結構調整 selector）---
SELECTOR_ARTICLE_LIST   = "div.member-blog-listm"    # 列表頁中包住文章連結的區塊
SELECTOR_ARTICLE_LINK   = 'a[href*="diary/detail"]'  # 文章連結
SELECTOR_NOTFOUND_TITLE = "div.cate-hero h2.title"   # Not Found 頁的標題元素
SELECTOR_NOTFOUND_COL   = "div.col-r"                # Not Found 頁的內容欄
NOTFOUND_TITLE_TEXT     = "Not Found"                # Not Found 頁標題應有的文字
NOTFOUND_MESSAGE_TEXT   = "ページが見つかりません"    # Not Found 頁的訊息文字
NO_ARTICLES_TEXT        = "記事がありません"          # 列表頁「沒有文章」的標示文字
# ============================================================


# === 成員對照表 (獨立於 members.json，可自行編輯新增/修改成員) ===
def load_members(MEMBERS_FILE):    
    if not os.path.exists(MEMBERS_FILE):
        print(f"!!! 找不到成員對照表檔案: {MEMBERS_FILE}")
        print("    請確認 members.json 與程式放在同一個資料夾。")
        return {}
    try:
        # 使用 utf-8-sig：可自動處理 Windows 記事本存檔時偷加的 BOM 字元，
        # 沒有 BOM 的一般 UTF-8 檔案也能正常讀取，兩種都相容。
        with open(MEMBERS_FILE, "r", encoding="utf-8-sig") as f:
            return json.load(f)
    except Exception as e:
        print(f"!!! 讀取 members.json 失敗: {e}")
        return {}


def ask_ssl_verification():
    """
    詢問使用者是否關閉 SSL 驗證。
    回傳值即為要傳給 requests 的 verify 參數：
        True  = 維持 SSL 驗證（預設、較安全）
        False = 關閉 SSL 驗證
    """
    print("=" * 60)
    print("【SSL 憑證驗證設定】")
    print("如果你在下載時遇到類似以下的錯誤：")
    print("    SSLError ... CERTIFICATE_VERIFY_FAILED")
    print("    unable to get local issuer certificate")
    print("（常見於公司內網 / 有做 SSL 攔截的網路環境）")
    print("可以選擇「關閉 SSL 驗證」來繞過此問題。")
    print("注意：關閉驗證會降低連線安全性，若非必要建議維持開啟。")
    print("=" * 60)

    while True:
        choice = input("是否要關閉 SSL 驗證？(y/N，直接按 Enter 為維持驗證): ").strip().lower()
        if choice in ("", "n", "no"):
            print(">> 維持 SSL 驗證（預設）\n")
            return True   # verify=True
        if choice in ("y", "yes"):
            print(">> 已關閉 SSL 驗證\n")
            return False  # verify=False
        print("!! 輸入無效，請輸入 y 或 n。")

class BaseWebArchiver:
    """通用網頁備份基底類別 (V3 穩健版)"""

    # 特殊回傳標記：代表「頁面不存在 / 已無更多內容」，用來和「下載失敗(None)」區分。
    # 用獨一無二的 object() 當標記，不會和 soup 或 None 混淆。
    PAGE_NOT_FOUND = object()

    def __init__(self, output_root="Downloads", verify_ssl=True):
        self.output_root = output_root

        # 若關閉 SSL 驗證，抑制 InsecureRequestWarning，避免每次請求都洗版
        if not verify_ssl:
            urllib3.disable_warnings(urllib3.exceptions.InsecureRequestWarning)

        # [改進 1] 建立 Session 並設定重試策略
        # 遇到連線錯誤、讀取超時、或伺服器回傳 5xx 錯誤時自動重試（參數見上方設定區）
        self.session = requests.Session()
        retries = Retry(
            total=MAX_RETRIES,
            backoff_factor=RETRY_BACKOFF,
            status_forcelist=RETRY_STATUS_CODES,
            allowed_methods=["GET"] # 只針對 GET 請求重試
        )
        # 掛載重試機制到 http 和 https
        self.session.mount("http://", HTTPAdapter(max_retries=retries))
        self.session.mount("https://", HTTPAdapter(max_retries=retries))
        
        # 設定偽裝 Header
        self.session.headers.update({
            "User-Agent": USER_AGENT
        })

        # 一次設定整個 Session 的 SSL 驗證行為，後續所有請求都會沿用
        self.session.verify = verify_ssl

        if not os.path.exists(self.output_root):
            os.makedirs(self.output_root)

    def _get_local_path_from_url(self, url):
        parsed = urlparse(url)
        domain = parsed.netloc.replace(":", "_")
        path = unquote(parsed.path)
        if path.startswith("/"): path = path[1:]
        if not os.path.splitext(path)[1]:
            path = os.path.join(path, "index.html")
        return os.path.join(self.output_root, domain, path)

    def download_asset(self, url, source_html_path):
        """下載資源，如果失敗會拋出異常 (Exception)"""
        if not url or url.strip().startswith(('data:', '#', 'mailto:', 'javascript:')):
            return url
        
        url = url.strip()
        local_abs_path = self._get_local_path_from_url(url)
        
        # 快取檢查
        if os.path.exists(local_abs_path):
            html_dir = os.path.dirname(source_html_path)
            rel_path = os.path.relpath(local_abs_path, html_dir)
            return rel_path.replace(os.sep, '/')

        # 開始下載
        os.makedirs(os.path.dirname(local_abs_path), exist_ok=True)
        try:
            # 使用 session.get (包含自動重試)
            resp = self.session.get(url, timeout=REQUEST_TIMEOUT)
            resp.raise_for_status() # 如果狀態碼不是 200，拋出異常
            
            with open(local_abs_path, 'wb') as f:
                f.write(resp.content)
            
            # 回傳相對路徑
            html_dir = os.path.dirname(source_html_path)
            rel_path = os.path.relpath(local_abs_path, html_dir)
            return rel_path.replace(os.sep, '/')

        except Exception as e:
            # [關鍵] 這裡不再只是 print，而是將錯誤往上拋
            # 讓上層知道這個檔案下載失敗了
            print(f"      [資源下載失敗] {url} : {e}")
            raise e 

    def _process_css_backgrounds(self, soup, url, html_local_path):
        url_pattern = re.compile(r'url\s*\(\s*([\'"]?)(.*?)\1\s*\)', re.IGNORECASE | re.DOTALL)
        tags = soup.find_all(style=re.compile(r'url\(', re.IGNORECASE))
        
        for tag in tags:
            old_style = tag['style']
            
            # 這裡我們需要一個 list 來捕捉內部函數的異常
            errors = []

            def replace_match(match):
                quote = match.group(1) if match.group(1) else ""
                original_src = match.group(2).strip()
                if not original_src: return match.group(0)
                full_url = urljoin(url, original_src)
                
                try:
                    new_rel_path = self.download_asset(full_url, html_local_path)
                    return f'url({quote}{new_rel_path}{quote})'
                except Exception:
                    errors.append(full_url)
                    return match.group(0) # 失敗則維持原樣

            new_style = url_pattern.sub(replace_match, old_style)
            tag['style'] = new_style
            
            # 如果處理 CSS 背景圖時發生錯誤，也拋出異常
            if errors:
                raise Exception(f"CSS Background image failed: {errors[0]}")

    def _is_not_found_page(self, soup):
        """
        依實際 HTML 結構判斷是否為官方的「頁面不存在」頁，避免用整頁字串比對造成誤判。
        參考結構：
            <div class="cate-hero"> ... <h2 class="title">Not Found</h2> ... </div>
            <div class="col-r"><p>ページが見つかりません</p></div>
        任一訊號命中即認定為 Not Found 頁。
        """
        # 訊號 1（最可靠）：hero 區塊標題剛好是 "Not Found"。
        # 正常頁的 hero 標題是成員名 / 部落格名，不會是 "Not Found"。
        hero_title = soup.select_one(SELECTOR_NOTFOUND_TITLE)
        if hero_title and hero_title.get_text(strip=True) == NOTFOUND_TITLE_TEXT:
            return True

        # 訊號 2：col-r 內有某個 <p> 的文字「剛好等於」該訊息。
        # 注意 div.col-r 是全站共用的內容欄，所以這裡用「完全相等」而非「包含」，
        # 以免正常文章內文只是提到這串字就被誤判。
        col_r = soup.select_one(SELECTOR_NOTFOUND_COL)
        if col_r:
            for para in col_r.find_all("p"):
                if para.get_text(strip=True) == NOTFOUND_MESSAGE_TEXT:
                    return True

        return False

    def process_page_content(self, url, save_filename, custom_processor=None):
        """核心處理邏輯：如果過程中任何資源下載失敗，就不存檔"""
        
        html_local_path = os.path.join(self.output_root, save_filename)
        
        try:
            print(f"   [下載頁面] {save_filename} ...")
            # 下載 HTML 本體
            resp = self.session.get(url, timeout=REQUEST_TIMEOUT)
            resp.encoding = 'utf-8'

            # HTTP 404：直接視為「頁面不存在」(正常翻到底)，而非下載失敗
            if resp.status_code == 404:
                print(f"   [頁面結束] HTTP 404: {save_filename}")
                return self.PAGE_NOT_FOUND

            resp.raise_for_status() # 其他非-2xx (例如 5xx，重試後仍失敗) 視為下載失敗
            soup = BeautifulSoup(resp.text, 'html.parser')

            # 依實際頁面結構判斷是否為官方「Not Found」頁（比純字串比對可靠，避免誤判）
            if self._is_not_found_page(soup):
                print(f"   [頁面結束] 偵測到官方 Not Found 頁面: {save_filename}")
                return self.PAGE_NOT_FOUND

            os.makedirs(os.path.dirname(html_local_path), exist_ok=True)

            # === 資源下載 (如果出錯會直接跳到 except) ===
            
            # 1. CSS
            for tag in soup.find_all('link', rel='stylesheet'):
                if tag.get('href'):
                    tag['href'] = self.download_asset(urljoin(url, tag['href']), html_local_path)

            # 2. JS
            for tag in soup.find_all('script'):
                if tag.get('src'):
                    tag['src'] = self.download_asset(urljoin(url, tag['src']), html_local_path)

            # 3. 圖片 (最常超時的地方)
            for tag in soup.find_all('img'):
                if tag.get('src'):
                    tag['src'] = self.download_asset(urljoin(url, tag['src']), html_local_path)
                    if tag.get('srcset'): del tag['srcset']
                    if tag.get('loading'): del tag['loading']
            
            # 4. 背景圖
            self._process_css_backgrounds(soup, url, html_local_path)

            # 5. 客製化邏輯
            if custom_processor:
                should_save = custom_processor(soup, html_local_path)
                if should_save is False:
                    # custom_processor 主動表示「不要存、停止」(例如列表頁判定已無文章)，
                    # 這也屬於「正常結束」，回傳 PAGE_NOT_FOUND 而非 None。
                    return self.PAGE_NOT_FOUND

            # === 如果程式跑到這裡，代表所有圖片都下載成功了 ===
            # 只有這時候才寫入 HTML 檔案
            with open(html_local_path, "w", encoding="utf-8") as f:
                f.write(str(soup))
            
            return soup

        except Exception as e:
            # [改進 2] 錯誤處理策略
            print(f"   !!! 頁面下載不完整，取消存檔: {save_filename}")
            print(f"       原因: {e}")
            
            # 確保檔案不存在 (如果之前有殘留或寫到一半，把它刪掉)
            if os.path.exists(html_local_path):
                try:
                    os.remove(html_local_path)
                    print("       已刪除不完整的檔案，下次執行時將重試。")
                except:
                    pass
            return None

class SakurazakaBlogArchiver(BaseWebArchiver):
    def __init__(self, member_id, member_name, verify_ssl=True):
        output_dir = os.path.join(BACKUP_ROOT, member_name)
        super().__init__(output_root=output_dir, verify_ssl=verify_ssl)
        self.member_id = member_id
        self.base_url = BASE_LIST_URL

        # 統計用：本次新增備份成功、以及下載失敗的文章 ID
        self.saved_articles = []
        self.failed_articles = []
        # 掃描是否因列表頁下載失敗而中途中止（用於最後提醒使用者可能沒抓完）
        self.scan_interrupted = False

    def run(self):
        page = 0
        while True:
            list_url = f"{self.base_url}?ima=0000&page={page}&ct={self.member_id}&cd=blog"
            list_filename = f"blog_list_{page}.html"
            
            print(f"\n=== 正在掃描列表第 {page + 1} 頁 ===")
            
            def process_list_page(soup, html_local_path):
                if NO_ARTICLES_TEXT in soup.get_text():
                    print(">>> 偵測到「無文章」標示，停止備份。")
                    return False

                target_area = soup.select_one(SELECTOR_ARTICLE_LIST)
                if target_area:
                    links = target_area.select(SELECTOR_ARTICLE_LINK)
                    
                    for a in links:
                        href = a.get('href')
                        full_article_url = urljoin(list_url, href)
                        
                        article_id = os.path.basename(urlparse(full_article_url).path)
                        article_filename = f"{ARTICLE_SUBDIR}/blog_{article_id}.html"
                        
                        full_local_path = os.path.join(self.output_root, article_filename)
                        
                        # [增量備份檢查]
                        if os.path.exists(full_local_path):
                            print(f"    [略過] 文章 {article_id} 已存在且完整。")
                        else:
                            # 嘗試下載
                            result = self.process_page_content(full_article_url, article_filename)
                            if result is self.PAGE_NOT_FOUND:
                                # 文章頁面不存在(可能已被刪除)，重試也沒用，不計入失敗清單
                                print(f"    [略過] 文章 {article_id} 頁面不存在，可能已被刪除。")
                            elif result is None:
                                print(f"    [警告] 文章 {article_id} 下載失敗，已跳過 (下次會重試)。")
                                self.failed_articles.append(article_id)
                            else:
                                self.saved_articles.append(article_id)
                        
                        a['href'] = article_filename.replace('\\', '/')
                        
                else:
                    print("    警告：找不到 member-blog-listm 區塊，可能版型有變。")

                self._add_navigation(soup, page)
                return True

            # 列表頁下載
            result = self.process_page_content(list_url, list_filename, custom_processor=process_list_page)

            if result is self.PAGE_NOT_FOUND:
                # 真的翻到底了（頁面不存在 / 無文章）→ 正常結束
                print("\n>>> 已無更多頁面，掃描正常結束。")
                break

            if result is None:
                # 列表頁本身「下載失敗」（網路錯誤 / 逾時），這不是到底，
                # 為避免漏抓後續頁面，中止並提醒使用者重跑。
                print("\n!!! 列表頁下載失敗（可能是網路問題），掃描已中止。")
                print("    這不代表已備份完成，請稍後重新執行以繼續。")
                self.scan_interrupted = True
                break

            page += 1
            time.sleep(PAGE_DELAY)

        # === 全部掃描結束後，統一印出本次結果 ===
        print("\n" + "=" * 60)
        print("備份掃描結果")

        if self.scan_interrupted:
            print("  ⚠ 注意：本次掃描因列表頁下載失敗而中途中止，")
            print("     可能還有頁面尚未備份，建議稍後重新執行。")

        if self.saved_articles:
            print(f"  本次新增備份 {len(self.saved_articles)} 篇文章。")
        else:
            print("  本次沒有新增文章（可能都已備份過，或該成員沒有文章）。")

        if self.failed_articles:
            print(f"\n  以下 {len(self.failed_articles)} 篇文章下載失敗（下次執行會自動重試）：")
            for aid in self.failed_articles:
                print(f"    - 文章 {aid}")
        else:
            print("  沒有下載失敗的文章。")
        print("=" * 60)

    def _add_navigation(self, soup, page):
        nav_html = f"""
        <div style="text-align:center; padding: 20px; background:#f4f4f4; margin-bottom:20px; border-bottom:1px solid #ddd;">
            <a href="blog_list_{max(0, page-1)}.html" style="margin-right:20px;">« 上一頁</a>
            <span>第 {page + 1} 頁</span>
            <a href="blog_list_{page+1}.html" style="margin-left:20px;">下一頁 »</a>
        </div>
        """
        if soup.body:
            soup.body.insert(0, BeautifulSoup(nav_html, 'html.parser'))

if __name__ == "__main__":
    
    MEMBERS_FILE = os.path.join(_APP_DIR, MEMBERS_FILENAME)
    MEMBERS = load_members(MEMBERS_FILE)

    # 讀不到任何成員資料（檔案不存在、格式錯誤、或內容為空）就直接結束
    if not MEMBERS:
        print("!!! 沒有讀取到任何成員資料，程式結束。")
        input("按 Enter 鍵關閉視窗...")  # 讓 .exe 直接雙擊執行時不會一閃就消失
        sys.exit(1)

    print("=== 櫻坂46 部落格備份小工具 (V2 exe包裝版) ===")
    print("\n[參考 ID]")
    for mid, mname in MEMBERS.items():
        print(f"  {mid}: {mname}")
    print("  ...")

    target_id = input("\n請輸入成員 ID (例如 43): ").strip()

    # 輸入無效時給明確訊息並結束，而不是靜默什麼都不做
    if not target_id or target_id not in MEMBERS:
        print(f"!!! 成員 ID「{target_id}」無效或不在對照表中，程式結束。")
        input("按 Enter 鍵關閉視窗...")
        sys.exit(1)

    folder_name = MEMBERS.get(target_id, f"Member_{target_id}")

    # 執行前詢問是否關閉 SSL 驗證
    verify_ssl = ask_ssl_verification()

    print(f"目標: {target_id}, 儲存資料夾: {folder_name}")
    print("開始執行...\n")

    archiver = SakurazakaBlogArchiver(
        member_id=target_id,
        member_name=folder_name,
        verify_ssl=verify_ssl,
    )
    archiver.run()

    print("\n" + "=" * 30)
    print("備份作業結束。")
    input("請按 Enter 鍵結束程式...")