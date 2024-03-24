import requests
from requests.adapters import HTTPAdapter, Retry
import re
import os
import math
from bs4 import BeautifulSoup
import time
import datetime
from PIL import Image
from io import BytesIO
import json
from numbers import Number
import pathlib
import itertools

from .args import get_args
from .logger import logger
from .version import __version__
from .helper import get_file_hash, print_download_bar, check_date, parse_url, compile_post_path, compile_file_path, RefererSession
from .my_yt_dlp import my_yt_dlp

class downloader:

    def __init__(self, args):
        self.input_urls = args['links'] + args['from_file']
        if args['cccp']:
            self.input_urls = [i.replace('.party','.su') for i in self.input_urls]
        # list of completed posts from current session
        self.comp_posts = []
        # list of creators info
        self.creators = []

        # requests variables
        self.headers = {'User-Agent': args['user_agent']} if args['user_agent'] else {}
        self.cookies = args['cookies']
        self.timeout = 300

        # file/folder naming
        self.download_path_template = args['dirname_pattern']
        self.filename_template = args['filename_pattern']
        self.inline_filename_template = args['inline_filename_pattern']
        self.other_filename_template = args['other_filename_pattern']
        self.user_filename_template = args['user_filename_pattern']
        self.date_strf_pattern = args['date_strf_pattern']
        self.yt_dlp_args = args['yt_dlp_args']
        self.restrict_ascii = args['restrict_names']

        self.archive_file = args['archive']
        self.archive_list = []
        self.post_errors = 0

        # controls what to download/save
        self.local_hash = not args['skip_local_hash']
        self.attachments = not args['skip_attachments']
        self.inline = args['inline']
        self.content = args['content']
        self.extract_links = args['extract_links']
        self.extract_all_links = args['extract_all_links']
        self.comments = args['comments']
        self.json = args['json']
        self.yt_dlp = args['yt_dlp']
        self.k_fav_posts = args['kemono_fav_posts']
        self.c_fav_posts = args['coomer_fav_posts']
        self.k_fav_users = args['kemono_fav_users']
        self.c_fav_users = args['coomer_fav_users']
        self.icon_banner = []
        if args['icon']:
            self.icon_banner.append('icon')
        if args['banner']:
            self.icon_banner.append('banner')
        self.dms = args['dms']
        self.announcements = args['announcements']

        # controls files to ignore
        self.overwrite = args['overwrite']
        self.only_ext = args['only_filetypes']
        self.not_ext = args['skip_filetypes']
        self.max_size = args['max_filesize']
        self.min_size = args['min_filesize']
        self.only_filename = args['only_filename']
        self.not_filename = args['skip_filename']

        # controlls posts to ignore
        self.date = args['date']
        self.datebefore = args['datebefore']
        self.dateafter = args['dateafter']
        self.user_up_datebefore = args['user_updated_datebefore']
        self.user_up_dateafter = args['user_updated_dateafter']
        self.only_postname = args['only_postname']
        self.not_postname = args['skip_postname']

        # other
        self.retry = args['retry']
        self.no_part = args['no_part_files']
        self.ratelimit_sleep = args['ratelimit_sleep']
        self.post_timeout = args['post_timeout']
        self.simulate = args['simulate']
        self.local_hash = args['local_hash']
        self.dupe_check = args['dupe_check']
        self.dupe_check_template = args['dupe_check_pattern']
        self.force_unlisted = args['force_unlisted']
        self.retry_403 = args['retry_403']
        self.fp_added = args['fp_added']
        self.cookie_domains = args['cookie_domains']
        self.fancards = args['fancards']
        self.cookie_domains = args['cookie_domains']

        self.session = RefererSession()
        retries = Retry(
            total=self.retry,
            backoff_factor=0.1,
            status_forcelist=[ 500, 502, 503, 504 ]
        )
        self.session.mount('https://', HTTPAdapter(max_retries=retries))
        self.session.mount('http://', HTTPAdapter(max_retries=retries))

        self.proxies = {'http': args['proxy'], 'https': args['proxy']}
        self.session.proxies = self.proxies

        self.start_download()

    def get_creators(self, domain:str):
        # get site creators
        creators_api = f"https://{domain}/api/v1/creators.txt"
        logger.debug(f"Getting creator json from {creators_api}")
        return self.session.get(url=creators_api, cookies=self.cookies, headers=self.headers, timeout=self.timeout).json()

    def get_user(self, user_id:str, service:str):
        for creator in self.creators:
            if creator['id'] == user_id and creator['service'] == service:
                return creator
        return None

    def get_favorites(self, domain:str, fav_type:str, retry:int, services:list = None):
        fav_api = f'https://{domain}/api/v1/account/favorites?type={fav_type}'
        logger.debug(f"Getting favorite json from {fav_api}")
        response = self.session.get(url=fav_api, headers=self.headers, cookies=self.cookies, timeout=self.timeout)
        if response.status_code == 401:
            logger.error(f"Failed to get favorites: {response.status_code} {response.reason} | Bad cookie file")
            return
        if not response.ok:
            if retry>0:
                logger.exception(f"Failed to get favorites: {response.status_code} {response.reason} | Retrying")
                self.get_favorites(domain=domain, fav_type=fav_type, retry=retry-1, services=services)
                return
            logger.error(f"Failed to get favorites: {response.status_code} {response.reason} | All retries failed")
            return
        for favorite in response.json():
            if fav_type == 'post':
                self.get_post(f"https://{domain}/{favorite['service']}/user/{favorite['user']}/post/{favorite['id']}", retry=self.retry)
            if fav_type == 'artist':
                if not (favorite['service'] in services or 'all' in services):
                    logger.info(f"Skipping user {favorite['name']} | Service {favorite['service']} was not requested")
                    continue
                self.get_post(f"https://{domain}/{favorite['service']}/user/{favorite['id']}", retry=self.retry)

    def get_post(self, url:str, retry:int, chunk=0, first=True):
        found = re.search(r'(https://((?:kemono|coomer)\.(?:party|su))/)(([^/]+)/user/([^/]+)($|/post/[^/]+))', url)
        if not found:
            logger.error(f"Unable to find url parameters for {url}")
            return
        api = f"{found.group(1)}api/v1/{found.group(3)}"
        site = found.group(2)
        service = found.group(4)
        user_id = found.group(5)
        is_post = found.group(6)
        user = self.get_user(user_id, service)
        if not user:
            if self.force_unlisted:
                user={'favorited': 0, 'id': user_id, 'indexed': 1666666666, 'name': user_id, 'service': service, 'updated': 1666666666}
            else:
                logger.error(f"Unable to find user info in creators list | {service} | {user_id}")
                return
        if not is_post:
            if self.skip_user(user):
                return
        logger.info(f"Downloading posts from {site} | {service} | {user['name']} | {user['id']}")
        while True:
            if is_post:
                logger.debug(f"Requesting post json from: {api}")
                response = self.session.get(url=api, cookies=self.cookies, headers=self.headers, timeout=self.timeout)
                if response.status_code == 429:
                    logger.warning(f"Failed to request post json from: {api} | 429 Too Many Requests | Sleeping for {self.ratelimit_sleep} seconds")
                    time.sleep(self.ratelimit_sleep)
                    if retry > 0:
                        self.get_post(url=url, retry=retry-1, chunk=chunk, first=first)
                    return
            else:
                logger.debug(f"Requesting user json from: {api}?o={chunk}")
                response = self.session.get(url=f"{api}?o={chunk}", cookies=self.cookies, headers=self.headers, timeout=self.timeout)
                if response.status_code == 429:
                    logger.warning(f"Failed to request user json from: {api}?o={chunk} | 429 Too Many Requests | Sleeping for {self.ratelimit_sleep} seconds")
                    time.sleep(self.ratelimit_sleep)
                    if retry > 0:
                        self.get_post(url=url, retry=retry-1, chunk=chunk, first=first)
                    return
            json = response.json()
            if not json:
                if is_post:
                    logger.error(f"Unable to find post json for {api}")
                elif chunk == 0:
                    logger.error(f"Unable to find user json for {api}?o={chunk}")
                return # completed
            if not isinstance(json,list):
                json=[json]
            for post in json:
                # only download once
                if not is_post and first:
                    try:
                        post_tmp = self.clean_post(post, user, site)
                        logger.debug(f"Downloading icon and/or banner | {user['name']} | {user['id']}")
                        self.download_icon_banner(post_tmp, self.icon_banner, retry=self.retry)
                        if self.dms:
                            logger.debug(f"Writting dms | {user['name']} | {user['id']}")
                            self.write_dms(post_tmp)
                        if self.fancards:
                            logger.debug(f"Downloading fancards | {user['name']} | {user['id']}")
                            self.download_fancards(post_tmp)
                        if self.announcements:
                            logger.debug(f"Writting announcements | {user['name']} | {user['id']}")
                            self.write_announcements(post_tmp)
                        first = False
                    except:
                        logger.warning(f"Failed to get icon, banner, dms, fancards or announcements | Probably 429 | Sleeping for {self.ratelimit_sleep} seconds")
                        time.sleep(self.ratelimit_sleep)
                        if retry > 0:
                            self.get_post(url=url, retry=retry-1, chunk=chunk, first=True)
                        return
                comments_original=self.comments
                self.comments=False

                try:
                    post_tmp = self.clean_post(post, user, site)
                except:
                    logger.warning(f"Failed to clean post for {api} | Probably 429 | Sleeping for {self.ratelimit_sleep} seconds")
                    time.sleep(self.ratelimit_sleep)
                    if retry > 0:
                        self.get_post(url=url, retry=retry-1, chunk=chunk, first=True)
                    return
                
                if self.skip_post(post_tmp):
                    continue
                self.comments=comments_original
                post = self.clean_post(post, user, site)
                try:
                    self.download_post(post)
                    if self.post_timeout:
                        logger.info(f"Sleeping for {self.post_timeout} seconds.")
                        time.sleep(self.post_timeout)
                except:
                    logger.exception("Unable to download post | service:{service} user_id:{user_id} post_id:{id}".format(**post['post_variables']))
                self.comp_posts.append("https://{site}/{service}/user/{user_id}/post/{id}".format(**post['post_variables']))
            min_chunk_size = 25
            # adapt chunk_size. I assume min chunck size is 25, and it should be a multiple of 25
            # for now kemono.party chunk size is 50
            # however coomer.party chunk size is 25
            chunk_size = math.ceil((len(json) / min_chunk_size)) * min_chunk_size
            logger.debug(f"Adaptive chunk_size set to {chunk_size}")
            if len(json) < chunk_size:
                return # completed
            chunk += chunk_size


    def download_icon_banner(self, post:dict, img_types:list, retry:int):
        for img_type in img_types:
            if post['post_variables']['service'] in {'dlsite'}:
                logger.warning(f"Profile {img_type}s are not supported for {post['post_variables']['service']} users")
                continue
            if post['post_variables']['service'] in {'gumroad'} and img_type == 'banner':
                logger.warning(f"Profile {img_type}s are not supported for {post['post_variables']['service']} users")
                continue
            image_url = "https://{site}/{img_type}s/{service}/{user_id}".format(img_type=img_type, **post['post_variables'])
            response = self.session.get(url=image_url,headers=self.headers, cookies=self.cookies, timeout=self.timeout)
            if response.status_code == 429:
                logger.warning(f"Unable to download profile {img_type} for {post['post_variables']['username']} | 429 Too Many Requests | Sleeping for {self.ratelimit_sleep} seconds")
                time.sleep(self.ratelimit_sleep)
                if retry > 0:
                    self.download_icon_banner(post=post, img_types=img_types, retry=retry-1)
                else:
                    logger.error(f"Unable to download profile {img_type} for {post['post_variables']['username']} | 429 Too Many Requests | All retry attemps failed")
                return
            try:
                image = Image.open(BytesIO(response.content))
                file_variables = {
                    'filename':img_type,
                    'ext':image.format.lower()
                }
                file_path = compile_file_path(post['post_path'], post['post_variables'], file_variables, self.user_filename_template, self.restrict_ascii)
                if os.path.exists(file_path):
                    logger.info(f"Skipping: {os.path.split(file_path)[1]} | File already exists")
                    continue
                logger.info(f"Downloading: {os.path.split(file_path)[1]}")
                logger.debug(f"Downloading to: {file_path}")
                if not self.simulate:
                    if not os.path.exists(os.path.split(file_path)[0]):
                        os.makedirs(os.path.split(file_path)[0])
                    image.save(file_path, format=image.format)
            except:
                logger.error(f"Unable to download profile {img_type} for {post['post_variables']['username']}")

    def write_dms(self, post:dict):
        # no api method to get comments so using from html (not future proof)
        if post['post_variables']['service'] != 'patreon':
            logger.debug("Skipping dms for non patreon user https://{site}/{service}/user/{user_id}".format(**post['post_variables']))
            return
        post_url = "https://{site}/{service}/user/{user_id}/dms".format(**post['post_variables'])
        response = self.session.get(url=post_url, allow_redirects=True, headers=self.headers, cookies=self.cookies, timeout=self.timeout)
        page_soup = BeautifulSoup(response.text, 'html.parser')
        if page_soup.find("div", {"class": "no-results"}):
            logger.info("No DMs found for https://{site}/{service}/user/{user_id}".format(**post['post_variables']))
            return
        dms_soup = page_soup.find("div", {"class": "card-list__items"})
        file_variables = {
            'filename':'direct messages',
            'ext':'html'
        }
        file_path = compile_file_path(post['post_path'], post['post_variables'], file_variables, self.user_filename_template, self.restrict_ascii)
        self.write_to_file(file_path, dms_soup.prettify())

    def download_fancards(self, post:dict):
        # there's api now, too lazy to rewrite
        if post['post_variables']['service'] != 'fanbox':
            logger.debug("Skipping fancards for non fanbox user https://{site}/{service}/user/{user_id}".format(**post['post_variables']))
            return
        post_url = "https://{site}/{service}/user/{user_id}/fancards".format(**post['post_variables'])
        logger.info(f"Downloading fancards {post_url}")
        response = self.session.get(url=post_url, allow_redirects=True, headers=self.headers, cookies=self.cookies, timeout=self.timeout)
        page_soup = BeautifulSoup(response.text, 'html.parser')
        if page_soup.find("div", {"class": "no-results"}):
            logger.info("No fancards found for https://{site}/{service}/user/{user_id}".format(**post['post_variables']))
            return
        fancards_soup = page_soup.find_all("article", {"class": "fancard__file"})
        for fancard in fancards_soup:
            fancard_title = fancard.find("span").getText()
            fancard_url = fancard.find("a", href=True)['href']
            fancard_filename_orig = fancard_url.split("/")[-1]
            fancard_filename, fancard_ext = fancard_filename_orig.split(".")
            file_variables = {
                'filename':'{title}_{name}'.format(title=fancard_title,name=fancard_filename),
                'ext':fancard_ext,
                'url':fancard_url,
                'hash':fancard_filename,
                'referer':post_url
            }
            file_path = compile_file_path(os.path.join(post['post_path'],'Fancards'), post['post_variables'], file_variables, self.user_filename_template, self.restrict_ascii)
            self.download_file({"file_path":file_path,"file_variables":file_variables}, retry=self.retry, post=post) #dummy postid

    def write_announcements(self, post:dict):
        post_url = "https://{site}/api/v1/{service}/user/{user_id}/announcements".format(**post['post_variables'])
        response = self.session.get(url=post_url, allow_redirects=True, headers=self.headers, cookies=self.cookies, timeout=self.timeout)
        if not response.ok:
            logger.error("Failed to download announcement, skipping...")
            return
        if not len(response.json()):
            logger.info("No announcements found for https://{site}/{service}/user/{user_id}".format(**post['post_variables']))
            return

        announcements = ""
        for announcement in response.json():
            ann_pub_date = f'published: {announcement.get("published")}'
            ann_add_date = f'added: {announcement.get("added")}'
            announcements += f'# {ann_pub_date} | {ann_add_date}\n\n'
            announcements += f'{announcement["content"].strip()}\n\n'

        file_variables = {
            'filename':'announcements',
            'ext':'txt'
        }
        file_path = compile_file_path(post['post_path'], post['post_variables'], file_variables, self.user_filename_template, self.restrict_ascii)
        overwrite_original = self.overwrite
        if os.path.exists(file_path) and os.path.getsize(file_path) < len(announcements):
            self.overwrite = True
        self.write_to_file(file_path, announcements)
        self.overwrite = overwrite_original

    def get_inline_images(self, post, content_soup):
        # only get images that are hosted by the .party site
        inline_images = [inline_image for inline_image in content_soup.find_all("img") 
                            if inline_image.get('src') and inline_image.get('src')[0] == '/']
        for index, inline_image in enumerate(inline_images):
            file = {}
            filename, file_extension = os.path.splitext(inline_image['src'].rsplit('/')[-1])
            m = re.search(r'[a-zA-Z0-9]{64}', inline_image['src'])
            file_hash = m.group(0) if m else None
            file['file_variables'] = {
                'filename': filename,
                'ext': file_extension[1:],
                'url': f"https://{post['post_variables']['site']}/data{inline_image['src']}",
                'hash': file_hash,
                'index': f"{index + 1}".zfill(len(str(len(inline_images)))),
                'referer': f"https://{post['post_variables']['site']}/{post['post_variables']['service']}/user/{post['post_variables']['user_id']}/post/{post['post_variables']['id']}"
            }
            file['file_path'] = compile_file_path(post['post_path'], post['post_variables'], file['file_variables'], self.inline_filename_template, self.restrict_ascii)
            html_loc = pathlib.Path(compile_file_path(post['post_path'], post['post_variables'], {'filename':'dummy','ext':'html'}, self.other_filename_template, self.restrict_ascii)).parent
            # set local image location in html
            inline_image['src'] = os.path.relpath(file['file_path'],html_loc)
            post['inline_images'].append(file)
        return content_soup

    def compile_content_links(self, post, content_soup, embed_links):
        href_links = content_soup.find_all(href=True)
        post['links']['text'] = embed_links
        for href_link in href_links:
            post['links']['text'] += f"{href_link['href']}\n"
        post['links']['file_variables'] = {
            'filename':'links',
            'ext':'txt'
        }
        post['links']['file_path'] = compile_file_path(post['post_path'], post['post_variables'], post['links']['file_variables'], self.other_filename_template, self.restrict_ascii)

    def get_comments(self, post_variables:dict, retry:int):
        try:
            # no api method to get comments so using from html (not future proof)
            post_url = "https://{site}/{service}/user/{user_id}/post/{id}".format(**post_variables)
            response = self.session.get(url=post_url, allow_redirects=True, headers=self.headers, cookies=self.cookies, timeout=self.timeout)
            if response.status_code == 429:
                logger.warning(f"Failed to get post comments | 429 Too Many Requests | Sleeping for {self.ratelimit_sleep} seconds")
                time.sleep(self.ratelimit_sleep)
                if retry > 0:
                    return self.get_comments(post_variables=post_variables, retry=retry-1)
            page_soup = BeautifulSoup(response.text, 'html.parser')
            comment_soup = page_soup.find("div", {"class": "post__comments"})
            no_comments = re.search('([^ ]+ does not support comment scraping yet\.|No comments found for this post\.)',comment_soup.text)
            if no_comments:
                logger.debug(no_comments.group(1).strip())
                return ''
            return comment_soup.prettify()
        except:
            self.post_errors += 1
            logger.exception("Failed to get post comments")

    def compile_post_content(self, post, content_soup, comment_soup, embed):
        post['content']['text'] = f"{content_soup}\n{embed}\n{comment_soup}"
        post['content']['file_variables'] = {
            'filename':'content',
            'ext':'html'
        }
        post['content']['file_path'] = compile_file_path(post['post_path'], post['post_variables'], post['content']['file_variables'], self.other_filename_template, self.restrict_ascii)

    def clean_post(self, post:dict, user:dict, domain:str):
        new_post = {}
        # set post variables
        new_post['post_variables'] = {}
        new_post['post_variables']['title'] = post['title']
        new_post['post_variables']['id'] = post['id']
        new_post['post_variables']['user_id'] = post['user']
        new_post['post_variables']['username'] = user['name']
        new_post['post_variables']['site'] = domain
        new_post['post_variables']['service'] = post['service']
        new_post['post_variables']['added'] = self.format_time_by_type(post['added']) if post['added'] else None
        new_post['post_variables']['updated'] = self.format_time_by_type(post['edited']) if post['edited'] else None
        new_post['post_variables']['user_updated'] = self.format_time_by_type(user['updated']) if user['updated'] else None
        new_post['post_variables']['published'] = self.format_time_by_type(post['published']) if post['published'] else None
        new_post['post_variables']['tags'] = post['tags']
        new_post['post_variables']['poll'] = post['poll']

        new_post['post_path'] = compile_post_path(new_post['post_variables'], self.download_path_template, self.restrict_ascii)

        new_post['attachments'] = []
        if self.attachments:
            # add post file to front of attachments list if it doesn't already exist
            if post['file'] and not post['file'] in post['attachments']:
                post['attachments'].insert(0, post['file'])
            # loop over attachments and set file variables
            for index, attachment in enumerate(post['attachments']):
                file = {}
                filename, file_extension = os.path.splitext(attachment['name'])
                m = re.search(r'[a-zA-Z0-9]{64}', attachment['path'])
                file_hash = m.group(0) if m else None
                file['file_variables'] = {
                    'filename': filename,
                    'ext': file_extension[1:],
                    'url': f"https://{domain}/data{attachment['path']}?f={attachment['name']}",
                    'hash': file_hash,
                    'index': f"{index + 1}".zfill(len(str(len(post['attachments'])))),
                    'referer': f"https://{domain}/{post['service']}/user/{post['user']}/post/{post['id']}"
                }
                file['file_path'] = compile_file_path(new_post['post_path'], new_post['post_variables'], file['file_variables'], self.filename_template, self.restrict_ascii)
                new_post['attachments'].append(file)

        new_post['inline_images'] = []
        content_soup = BeautifulSoup(post['content'], 'html.parser')
        if self.inline:
            content_soup = self.get_inline_images(new_post, content_soup)

        comment_soup = self.get_comments(new_post['post_variables'], retry=self.retry) if self.comments else ''

        new_post['content'] = {'text':None,'file_variables':None, 'file_path':None}
        embed = "{subject}\n{url}\n{description}".format(**post['embed']) if post['embed'] else ''
        if (self.content or self.comments) and (content_soup or comment_soup or embed):
            self.compile_post_content(new_post, content_soup.prettify(), comment_soup, embed)

        new_post['links'] = {'text':None,'file_variables':None, 'file_path':None}
        embed_url = "{url}\n".format(**post['embed']) if post['embed'] else ''
        if self.extract_links or self.extract_all_links:
            self.compile_content_links(new_post, content_soup, embed_url)

        return new_post

    def download_post(self, post:dict):
        # might look buggy if title has new lines in it
        logger.info("Downloading Post | {title}".format(**post['post_variables']))
        logger.debug("Post URL: https://{site}/{service}/user/{user_id}/post/{id}".format(**post['post_variables']))
        self.download_attachments(post)
        self.download_inline(post)
        self.write_content(post)
        self.write_links(post)
        if self.json:
            self.write_json(post)
        self.download_yt_dlp(post)
        self.write_archive(post)
        self.post_errors = 0

    def download_attachments(self, post:dict):
        # download the post attachments
        for file in post['attachments']:
            try:
                self.download_file(file, retry=self.retry, post=post)
            except:
                self.post_errors += 1
                logger.exception(f"Failed to download: {file['file_path']}")

    def download_inline(self, post:dict):
        # download the post inline files
        for file in post['inline_images']:
            try:
                self.download_file(file, retry=self.retry, post=post)
            except:
                self.post_errors += 1
                logger.exception(f"Failed to download: {file['file_path']}")

    def write_content(self, post:dict):
        # write post content
        if post['content']['text']:
            try:
                self.write_to_file(post['content']['file_path'], post['content']['text'])
            except:
                self.post_errors += 1
                logger.exception(f"Failed to save content")

    def write_links(self, post:dict):
        # Write post content links
        if post['links']['text']:
            try:
                if self.extract_all_links:
                    self.write_links_to_file(f".\{post['post_variables']['username']}.txt", post['links']['text'])
                if self.extract_links:
                    self.write_to_file(post['links']['file_path'], post['links']['text'])
            except:
                self.post_errors += 1
                logger.exception(f"Failed to save content links")


    def write_json(self, post:dict):
        try:
            # add this to clean post function
            file_variables = {
                'filename':'json',
                'ext':'json'
            }
            file_path = compile_file_path(post['post_path'], post['post_variables'], file_variables, self.other_filename_template, self.restrict_ascii)
            self.write_to_file(file_path, post)
        except:
            self.post_errors += 1
            logger.exception(f"Failed to save json")

    def write_to_file(self, file_path, file_content):
        # check if file exists and if should overwrite
        if os.path.exists(file_path) and not self.overwrite:
            logger.info(f"Skipping: {os.path.split(file_path)[1]} | File already exists")
            return
        logger.info(f"Writing: {os.path.split(file_path)[1]}")
        logger.debug(f"Writing to: {file_path}")
        if not self.simulate:
            # create folder path if it doesn't exist
            if not os.path.exists(os.path.split(file_path)[0]):
                os.makedirs(os.path.split(file_path)[0])
            # write to file
            if isinstance(file_content, dict):
                with open(file_path,'w') as f:
                    json.dump(file_content, f, indent=4, sort_keys=True)
            else:
                with open(file_path,'wb') as f:
                    f.write(file_content.encode("utf-8"))

    def write_links_to_file(self, file_path, file_content):
        with open(file_path,'a') as f:
            print(file_content, file=f)

    def download_file(self, file:dict, retry:int, post:dict):
        # download a file
        if self.skip_file(file,post=post):
            return

        part_file = f"{file['file_path']}.part" if not self.no_part else file['file_path']

        logger.info(f"Downloading: {os.path.split(file['file_path'])[1]}")
        logger.debug(f"Downloading from: {file['file_variables']['url']}")
        logger.debug(f"Downloading to: {part_file}")

        # try to resume part file
        resume_size = 0
        if os.path.exists(part_file) and not self.overwrite:
            resume_size = os.path.getsize(part_file)
            logger.info(f"Trying to resuming partial download | Resume size: {resume_size} bytes")

        try:
            response = self.session.get(url=file['file_variables']['url'], stream=True, headers={**self.headers,'Range':f"bytes={resume_size}-", 'Referer':file['file_variables']['referer']}, cookies=self.cookies, timeout=self.timeout)
        except:
            logger.exception(f"Failed to get responce: {file['file_variables']['url']} | Retrying")
            if retry > 0:
                self.download_file(file, retry=retry-1, post=post)
                return
            logger.error(f"Failed to get responce: {file['file_variables']['url']} | All retries failed")
            self.post_errors += 1
            return

        # responce status code checking
        if response.status_code == 404:
            logger.error(f"Failed to download: {os.path.split(file['file_path'])[1]} | 404 Not Found")
            self.post_errors += 1
            return

        if response.status_code == 403:
            for _ in range(self.retry_403):
                logger.info('A 403 encountered, retry without session.')
                try:
                    response = requests.get(url=file['file_variables']['url'], stream=True, headers={'Range':f"bytes={resume_size}-", 'Referer':file['file_variables']['referer']}, timeout=self.timeout,proxies=self.proxies)
                except:
                    logger.exception(f"Failed to get responce: {file['file_variables']['url']} | Retrying")
                    if retry > 0:
                        self.download_file(file, retry=retry-1, post=post)
                        return
                    logger.error(f"Failed to get responce: {file['file_variables']['url']} | All retries failed")
                    self.post_errors += 1
                    return
                if response.status_code != 403:
                    break
            if response.status_code == 403:
                logger.error(f"Failed to download: {os.path.split(file['file_path'])[1]} | 403 Forbidden")
                self.post_errors += 1
                return

        if response.status_code == 416:
            logger.warning(f"Failed to download: {os.path.split(file['file_path'])[1]} | 416 Range Not Satisfiable | Assuming broken server hash value")
            content_length = self.session.get(url=file['file_variables']['url'], stream=True, headers=self.headers, cookies=self.cookies, timeout=self.timeout).headers.get('content-length', '')
            if content_length == resume_size:
                logger.debug("Correct amount of bytes downloaded | Assuming download completed successfully")
                if self.overwrite:
                    os.replace(part_file, file['file_path'])
                else:
                    os.rename(part_file, file['file_path'])
                return
            logger.error("Incorrect amount of bytes downloaded | Something went so wrong I have no idea what happened | Saving file with suffix in name")
            # os.remove(part_file)
            filepath=os.path.splitext(file['file_path'])
            filepath=filepath[0]+'_statuscode416'+filepath[1]
            if self.overwrite:
                os.replace(part_file, filepath)
            else:
                os.rename(part_file, filepath)
            self.post_errors += 1
            return

        if response.status_code == 429:
            logger.warning(f"Failed to download: {os.path.split(file['file_path'])[1]} | 429 Too Many Requests | Sleeping for {self.ratelimit_sleep} seconds")
            time.sleep(self.ratelimit_sleep)
            if retry > 0:
                self.download_file(file, retry=retry-1, post=post)
                return
            logger.error(f"Failed to download: {os.path.split(file['file_path'])[1]} | 429 Too Many Requests | All retries failed")
            self.post_errors += 1
            return
        if not response.ok:
            logger.error(f"Failed to download: {os.path.split(file['file_path'])[1]} | {response.status_code} {response.reason}")
            self.post_errors += 1
            return

        total = int(response.headers.get('content-length', 0))
        if total:
            total += resume_size

        if not self.simulate:
            try:
                if not os.path.exists(os.path.split(file['file_path'])[0]):
                    os.makedirs(os.path.split(file['file_path'])[0])
                with open(part_file, 'wb' if resume_size == 0 else 'ab') as f:
                    start = time.time()
                    downloaded = resume_size
                    iter_chunk_size = 256<<10
                    puff = bytes()
                    for chunk in response.iter_content(chunk_size=iter_chunk_size):
                        puff += chunk
                        downloaded += len(chunk)
                        if len(puff) >= (32<<20)//iter_chunk_size*iter_chunk_size:
                            f.write(puff)
                            puff = bytes()
                        print_download_bar(total, downloaded, resume_size, start)
                    if puff:
                        f.write(puff)
                        puff = bytes()
                print()
            except Exception as exc:
                # assuming puffered content is good
                with open(part_file, 'wb' if resume_size == 0 else 'ab') as f:
                    f.write(puff)
                    puff = bytes()
                if retry > 0:
                    logger.error(f"Failed to download: {os.path.split(file['file_path'])[1]} | Exception: {exc} | Retrying")
                    self.download_file(file, retry=retry-1, post=post)
                    return
                logger.error(f"Failed to download: {os.path.split(file['file_path'])[1]} | Exception: {exc} | All retries failed")
                self.post_errors += 1
                return

            # verify download
            local_hash = get_file_hash(part_file)
            logger.debug(f"Local File hash: {local_hash}")
            logger.debug(f"Sever File hash: {file['file_variables']['hash']}")
            if local_hash != file['file_variables']['hash']:
                if file['file_variables']['hash'] !=None:
                    logger.warning(f"File hash did not match server! | Retrying")
                    if os.path.getsize(part_file)==total:
                        os.remove(part_file)
                    if retry > 0:
                        self.download_file(file, retry=retry-1, post=post)
                        return
                    logger.error(f"File hash did not match server! | All retries failed")
                    self.post_errors += 1
                    return
                else:
                    logger.warning(f"No hash from server! | Saving file with suffix in name")
                    filepath=os.path.splitext(file['file_path'])
                    filepath=filepath[0]+'_noserverhash'+filepath[1]
                    if self.overwrite:
                        os.replace(part_file, filepath)
                    else:
                        os.rename(part_file, filepath)
                    return
            # remove .part from file name
            if self.overwrite:
                os.replace(part_file, file['file_path'])
            else:
                os.rename(part_file, file['file_path'])

    def download_yt_dlp(self, post:dict):
        # download from video streaming site
        # if self.yt_dlp and post['embed']:
            pass
            # my_yt_dlp(post['embed']['url'], post['post_path'], self.yt_dlp_args)

    def load_archive(self):
        # load archived posts
        if self.archive_file and os.path.exists(self.archive_file):
            with open(self.archive_file,'r') as f:
                self.archive_list = f.read().splitlines()

    def write_archive(self, post:dict):
        if self.archive_file and self.post_errors == 0 and not self.simulate:
            with open(self.archive_file,'a') as f:
                f.write("https://{site}/{service}/user/{user_id}/post/{id}".format(**post['post_variables']) + '\n')

    def skip_user(self, user:dict):
        # check last update date
        if self.user_up_datebefore or self.user_up_dateafter:
            if check_date(self.get_date_by_type(user['updated']), None, self.user_up_datebefore, self.user_up_dateafter):
                logger.info(f"Skipping user {user['id']} | user updated date not in range")
                return True
        return False

    def skip_post(self, post:dict):
        # check if the post should be downloaded
        if self.archive_file:
            post_url = "https://{site}/{service}/user/{user_id}/post/{id}".format(**post['post_variables'])
            post_url_another = post_url.replace('.su','.party') if post['post_variables']['site'].endswith('.su') else post_url.replace('.party','.su')
            if post_url in self.archive_list or post_url_another in self.archive_list:
                logger.info(f"Skipping post {post['post_variables']['id']} | post already archived") # add some numbers to indicate that the script isn't frozen when a lot of posts skipped and your screen is full of this message
                return True

        if self.date or self.datebefore or self.dateafter:
            if not post['post_variables']['published']:
                logger.info(f"Skipping post {post['post_variables']['id']} | post published date not in range")
                return True
            elif check_date(self.get_date_by_type(post['post_variables']['published' if not self.fp_added else 'added'], self.date_strf_pattern), self.date, self.datebefore, self.dateafter):
                logger.info(f"Skipping post {post['post_variables']['id']} | post published date not in range")
                return True

        if "https://{site}/{service}/user/{user_id}/post/{id}".format(**post['post_variables']) in self.comp_posts:
            logger.info(f"Skipping post {post['post_variables']['id']} | post was already downloaded this session")
            return True

        # check post title
        if self.only_postname:
            skip = True
            for w in self.only_postname:
                if w.lower() in post['post_variables']['title'].lower():
                    skip = False
                    break
            if skip:
                logger.info(f"Skipping post {post['post_variables']['id']} | post title does not contain any of the given word(s): {self.only_postname}")
                return True
                
        if self.not_postname:
            for w in self.not_postname:
                if w.lower() in post['post_variables']['title'].lower():
                    logger.info(f"Skipping post {post['post_variables']['id']} | post title contains word: {w}")
                    return True
        
        return False

    def skip_file(self, file:dict, post:dict):
        # check if file exists
        if not self.overwrite:
            if os.path.exists(file['file_path']):
                confirm_msg = ''
                if 'hash' in file['file_variables'] and file['file_variables']['hash'] != None and self.local_hash:
                    local_hash = get_file_hash(file['file_path'])
                    if local_hash != file['file_variables']['hash']:
                        logger.warning(f"Corrupted file detected, remove this file and try to redownload | path: {file['file_path']} " + 
                                        f"local hash: {local_hash} server hash: {file['file_variables']['hash']}")
                        os.remove(file['file_path'])
                        return False
                    confirm_msg = ' | Hash confirmed'
                logger.info(f"Skipping: {os.path.split(file['file_path'])[1]} | File already exists{confirm_msg}")
                return True
            if self.dupe_check:
                if file["file_variables"].get("index") is not None:
                    fp_cur=pathlib.Path(file['file_path'])
                    fp_par=fp_cur.parent
                    templates=self.dupe_check_template.split(',')
                    pattern=templates[0].format(**file['file_variables'], **post['post_variables'])
                    pattern2=templates[1].format(**file['file_variables'], **post['post_variables'])
                    similar=fp_par.glob(pattern)
                    similar2=fp_par.parent.glob(pattern2)
                    for x in itertools.chain(similar,similar2):
                        if 'hash' in file['file_variables'] and file['file_variables']['hash'] != None:
                            sim_hash = get_file_hash(str(x))
                            if sim_hash == file['file_variables']['hash']:
                                if x.suffix == '.part':
                                    os.rename(x,x.parent/x.stem)
                                logger.info(f"Skipping: {os.path.split(file['file_path'])[1]} | Same hash file exists")
                                return True

        # check file name extention
        if self.only_ext:
            if not file['file_variables']['ext'].lower() in self.only_ext:
                logger.info(f"Skipping: {os.path.split(file['file_path'])[1]} | File extention {file['file_variables']['ext']} not found in include list {self.only_ext}")
                return True
        if self.not_ext:
            if file['file_variables']['ext'].lower() in self.not_ext:
                logger.info(f"Skipping: {os.path.split(file['file_path'])[1]} | File extention {file['file_variables']['ext']} found in exclude list {self.not_ext}")
                return True

        # check file name 
        if self.only_filename:
            skip = True
            for w in self.only_filename:
                if w.lower() in file['file_variables']['filename'].lower():
                    skip = False
            if skip:
                logger.info(f"Skipping: {os.path.split(file['file_path'])[1]} | File name does not contain any of the given word(s): {self.only_filename} ")
                return True
                
        if self.not_filename:
            for w in self.not_filename:
                if w.lower() in file['file_variables']['filename'].lower():
                    logger.info(f"Skipping: {os.path.split(file['file_path'])[1]} | File name contains word: {w}")
                    return True

        # check file size
        if self.min_size or self.max_size:
            file_size = requests.get(file['file_variables']['url'], cookies=self.cookies, stream=True,proxies=self.proxies).headers.get('content-length', 0)
            if int(file_size) == 0:
                    logger.info(f"Skipping: {os.path.split(file['file_path'])[1]} | File size not included in file header")
                    return True
            if self.min_size and self.max_size:
                if not (self.min_size <= int(file_size) <= self.max_size):
                    logger.info(f"Skipping: {os.path.split(file['file_path'])[1]} | File size in bytes {file_size} was not between {self.min_size} and {self.max_size}")
                    return True
            elif self.min_size:
                if not (self.min_size <= int(file_size)):
                    logger.info(f"Skipping: {os.path.split(file['file_path'])[1]} | File size in bytes {file_size} was not >= {self.min_size}")
                    return True
            elif self.max_size:
                if not (int(file_size) <= self.max_size):
                    logger.info(f"Skipping: {os.path.split(file['file_path'])[1]} | File size in bytes {file_size} was not <= {self.max_size}")
                    return True
        return False



    def start_download(self):
        # start the download process
        self.load_archive()

        urls = []
        domains = []

        for url in self.input_urls:
            domain = parse_url(url)
            if not domain:
                logger.warning(f"URL is not downloadable | {url}")
                continue
            if domain not in self.cookie_domains.values() and self.cookies is not None:
                logger.warning(f"Domain not in cookie files, cookie won't work properly | {url}")
            urls.append(url)
            if not domain in domains: domains.append(domain)

        if self.k_fav_posts or self.k_fav_users:
            if self.cookie_domains['kemono'] not in domains:
                domains.append(self.cookie_domains['kemono'])
        if self.c_fav_posts or self.c_fav_users:
            if self.cookie_domains['coomer'] not in domains:
                domains.append(self.cookie_domains['coomer'])

        for domain in domains:
            try:
                self.creators += self.get_creators(domain)
            except:
                logger.exception(f"Unable to get list of creators from {domain}")
        if not self.creators:
            logger.error("No creator information was retrieved. | exiting")
            exit()

        if self.k_fav_posts:
            try:
                self.get_favorites(self.cookie_domains['kemono'], 'post', retry=self.retry)
            except:
                logger.exception(f"Unable to get favorite posts from {self.cookie_domains['kemono']}")
        if self.c_fav_posts:
            try:
                self.get_favorites(self.cookie_domains['coomer'], 'post', retry=self.retry)
            except:
                logger.exception(f"Unable to get favorite posts from {self.cookie_domains['coomer']}")
        if self.k_fav_users:
            try:
                self.get_favorites(self.cookie_domains['kemono'], 'artist', retry=self.retry, services=self.k_fav_users)
            except:
                logger.exception(f"Unable to get favorite users from {self.cookie_domains['kemono']}")
        if self.c_fav_users:
            try:
                self.get_favorites(self.cookie_domains['coomer'], 'artist', retry=self.retry, services=self.c_fav_users)
            except:
                logger.exception(f"Unable to get favorite users from {self.cookie_domains['coomer']}")

        for url in urls:
            try:
                self.get_post(url, retry=self.retry)
            except:
                logger.exception(f"Unable to get posts for {url}")

    def get_date_by_type(self, time, date_format = None):
        if isinstance(time, Number):
            t = datetime.datetime.fromtimestamp(time)
        elif isinstance(time, str):
            if date_format is None:
                try:
                    t = datetime.datetime.fromisoformat(time)
                except ValueError:
                    t = datetime.datetime.strptime(time, r'%Y%m%d')
            else:
                t = datetime.datetime.strptime(time, date_format)
        elif time == None:
            return None
        else:
            raise Exception(f'Can not format time {time}')
        return t
                
    def format_time_by_type(self, time):
        t = self.get_date_by_type(time)
        return t.strftime(self.date_strf_pattern) if t != None else t

def main():
    downloader(get_args())
